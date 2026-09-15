// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Runtime namespace resolver.
//!
//! The launch planner has already resolved every `DT_NEEDED` string to an
//! exact VFS path and acquired the complete system closure atomically. This
//! adapter therefore performs no search and takes no new system permit while
//! the linker owns mapped memory: it only replays planned requester/edge
//! bindings, opens the planned files, and consumes the prepared permits or
//! leases.

use alloc::{sync::Arc, vec::Vec};

use blueos_loader::{
    ArtifactIdentity, ArtifactResolver, DependencyName, DependencyRequest, DependencyResolution,
    ErrorContext, FileIdentity, ImageOwnership, ImportedImageDescriptor, LoadError, LoadErrorKind,
    LoadResult, ResolvedArtifact,
};

use crate::{
    application::{
        planner::{NamespaceLoadPlan, PlannedImage},
        registry::{
            AcquireBatchOutcome, LoadPermit, PreparedSystemBatch, SystemDsoLease, SystemDsoRegistry,
        },
    },
    vfs::open_path,
};

use super::vfs_reader::VfsElfReader;

struct SystemCandidateClaim {
    key: DependencyName,
    identity: ArtifactIdentity,
    permit: LoadPermit,
}

struct SystemImportClaim {
    key: DependencyName,
    descriptor: Arc<blueos_loader::PublishedImageDescriptor>,
}

/// One first-load system image and its unique registry publication authority.
pub struct SystemCandidatePermit {
    pub key: DependencyName,
    pub identity: ArtifactIdentity,
    pub permit: LoadPermit,
}

/// Registry authority accumulated while replaying a namespace plan.
pub struct ResolverAuthorities {
    pub permits: Vec<SystemCandidatePermit>,
    pub leases: Vec<SystemDsoLease>,
    /// Identity-to-canonical-key mapping for every system image in the plan.
    /// Publication uses this instead of optional ELF SONAME metadata.
    pub system_images: Vec<(ArtifactIdentity, DependencyName)>,
}

/// Resolve a fully planned application namespace into linker artifacts.
pub struct NamespaceArtifactResolver {
    plan: NamespaceLoadPlan,
    batch_loads: Vec<(DependencyName, LoadPermit)>,
    batch_imports: Vec<(
        DependencyName,
        SystemDsoLease,
        Arc<blueos_loader::PublishedImageDescriptor>,
    )>,
    candidates: Vec<SystemCandidateClaim>,
    leases: Vec<SystemDsoLease>,
    imports: Vec<SystemImportClaim>,
    opened_private: Vec<ArtifactIdentity>,
}

impl NamespaceArtifactResolver {
    /// Atomically acquire the plan's whole system closure. Waiting and retrying
    /// happens here, before the dynamic linker allocates an image.
    pub fn new(plan: NamespaceLoadPlan, registry: SystemDsoRegistry) -> LoadResult<Self> {
        let PreparedSystemBatch { loads, imports } = loop {
            match registry.acquire_batch(plan.system_keys()) {
                AcquireBatchOutcome::Acquired(batch) => break batch,
                AcquireBatchOutcome::Pending(wait) => wait.wait(),
            }
        };
        Ok(Self {
            plan,
            batch_loads: loads,
            batch_imports: imports,
            candidates: Vec::new(),
            leases: Vec::new(),
            imports: Vec::new(),
            opened_private: Vec::new(),
        })
    }

    /// Open the planned root artifact.
    pub fn root_artifact(&self) -> LoadResult<ResolvedArtifact<VfsElfReader>> {
        self.open_planned(&self.plan.images()[0], ImageOwnership::SessionPrivate)
    }

    /// Hand all registry authority to the publisher after dependency closure.
    pub fn finish_resolution(&mut self) -> ResolverAuthorities {
        let permits = core::mem::take(&mut self.candidates)
            .into_iter()
            .map(|claim| SystemCandidatePermit {
                key: claim.key,
                identity: claim.identity,
                permit: claim.permit,
            })
            .collect();
        let mut leases = core::mem::take(&mut self.leases);
        leases.extend(
            core::mem::take(&mut self.batch_imports)
                .into_iter()
                .map(|(_, lease, _)| lease),
        );
        let system_images = self
            .plan
            .images()
            .iter()
            .filter_map(|image| {
                image
                    .system_key()
                    .map(|key| (image.identity().clone(), key.clone()))
            })
            .collect();
        ResolverAuthorities {
            permits,
            leases,
            system_images,
        }
    }

    fn open_planned(
        &self,
        image: &PlannedImage,
        ownership: ImageOwnership,
    ) -> LoadResult<ResolvedArtifact<VfsElfReader>> {
        let file = open_path(image.path(), libc::O_RDONLY, 0).map_err(|_| backend_error())?;
        let reader = VfsElfReader::new(file);
        let identity = image.identity().clone();
        Ok(ResolvedArtifact::new(identity, ownership, reader))
    }

    fn planned_provider_index(&self, request: &DependencyRequest<'_>) -> LoadResult<usize> {
        let requester = self
            .plan
            .images()
            .iter()
            .position(|image| image.identity() == request.requester().identity())
            .ok_or_else(backend_error)?;
        self.plan
            .edges()
            .iter()
            .find(|edge| edge.requester() == requester && edge.request() == request.needed())
            .map(|edge| edge.provider())
            .ok_or_else(|| unresolved(request.needed()))
    }

    fn resolve_system(
        &mut self,
        provider_index: usize,
    ) -> LoadResult<DependencyResolution<VfsElfReader>> {
        let provider = &self.plan.images()[provider_index];
        let key = provider.system_key().ok_or_else(backend_error)?.clone();

        if let Some(claim) = self.candidates.iter().find(|claim| claim.key == key) {
            if claim.identity != *provider.identity() {
                return Err(backend_error());
            }
            return self
                .open_planned(provider, ImageOwnership::SystemCandidate)
                .map(DependencyResolution::Load);
        }

        if let Some((_, permit)) = take_by_key(&mut self.batch_loads, &key, |item| &item.0) {
            let artifact = self.open_planned(provider, ImageOwnership::SystemCandidate)?;
            self.candidates.push(SystemCandidateClaim {
                key: key.clone(),
                identity: provider.identity().clone(),
                permit,
            });
            log::info!("DSO_LOAD path={}", provider.path());
            return Ok(DependencyResolution::Load(artifact));
        }

        if let Some((_, lease, descriptor)) =
            take_by_key(&mut self.batch_imports, &key, |item| &item.0)
        {
            if descriptor.identity() != provider.identity() {
                return Err(backend_error());
            }
            self.leases.push(lease);
            self.imports.push(SystemImportClaim {
                key: key.clone(),
                descriptor: descriptor.clone(),
            });
            log::info!("DSO_REUSE path={}", provider.path());
            return Ok(DependencyResolution::Import(ImportedImageDescriptor::new(
                descriptor,
            )));
        }

        if let Some(claim) = self.imports.iter().find(|claim| claim.key == key) {
            return Ok(DependencyResolution::Import(ImportedImageDescriptor::new(
                claim.descriptor.clone(),
            )));
        }
        Err(backend_error())
    }
}

impl ArtifactResolver for NamespaceArtifactResolver {
    type Reader = VfsElfReader;

    fn resolve(
        &mut self,
        request: &DependencyRequest<'_>,
    ) -> LoadResult<DependencyResolution<Self::Reader>> {
        let provider_index = self.planned_provider_index(request)?;
        if self.plan.images()[provider_index].system() {
            self.resolve_system(provider_index)
        } else {
            let provider = &self.plan.images()[provider_index];
            if !self.opened_private.contains(provider.identity()) {
                log::info!("NS_LOAD path={}", provider.path());
                self.opened_private.push(provider.identity().clone());
            }
            self.open_planned(provider, ImageOwnership::SessionPrivate)
                .map(DependencyResolution::Load)
        }
    }
}

fn take_by_key<T>(
    items: &mut Vec<T>,
    key: &DependencyName,
    key_of: impl Fn(&T) -> &DependencyName,
) -> Option<T> {
    let position = items.iter().position(|item| key_of(item) == key)?;
    Some(items.swap_remove(position))
}

/// Use the normalized path as the loader's identity for this launch.
pub(crate) fn identity_from_path(path: &str) -> ArtifactIdentity {
    ArtifactIdentity::new(FileIdentity::from_bytes(path.as_bytes()))
}

fn backend_error() -> LoadError {
    LoadError::new(LoadErrorKind::Backend, ErrorContext::None)
}

fn unresolved(needed: &DependencyName) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Dependency {
            requester: 0,
            needed: needed.as_bytes().into(),
        },
    )
}
