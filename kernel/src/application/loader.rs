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

//! `ApplicationLoader`: the staged link driver and registry hand-off.
//!
//! [`ApplicationLoader`] is the bridge between the loader's neutral staged API
//! and the kernel's VFS/memory/cache/registry services. It drives
//! `DynamicLinker` through the `begin → close_dependencies → finish_resolution
//! → freeze_scopes → relocate → seal → publish` sequence, hands the
//! resolver's accumulated registry authority to the kernel link publisher, and
//! — once `publish` returns the committed [`LinkProduct`] — advances every
//! first-loading system candidate through the registry to `Ready` by its
//! canonical catalog path.
//!
//! The loader is a cloneable handle: it keeps the fixed catalog, the shared
//! registry and the shared-flat memory service, and mints a fresh linker,
//! resolver, cache and publisher per link. It performs no thread creation and
//! does not install the product into the group — the [`crate::application::manager`]
//! `prepare` closure builds the start storage and calls
//! [`ThreadGroup::install_resources`](crate::application::group::ThreadGroup::install_resources)
//! after this returns, so the infallible install is the manager's last step

use alloc::vec::Vec;

use blueos_loader::{
    AllocationLease, ArchitectureCodeCache, ArtifactIdentity, CacheRequirements, DependencyName,
    DynamicLinker, ImageOwnership, LinkProduct, LoadError, LoadErrorKind, LoadProfile, LoadResult,
    SessionLimits,
};

use blueos_loader::ArmRelocator as PlatformRelocator;

use crate::application::{
    adapters::{
        resolver::{NamespaceArtifactResolver, ResolverAuthorities, SystemCandidatePermit},
        system_paths::SystemLibraryPaths,
    },
    group::ThreadGroup,
    planner::NamespaceLoadPlan,
    publication::{KernelLinkPublisher, KernelLinkReceipt},
    registry::{SystemCandidateBacking, SystemDsoRegistry, SystemInitBatch},
};

/// A cloneable handle that links a dynamic application against the shared-flat
/// memory service and publishes its first-loading system DSOs.
pub struct ApplicationLoader {
    catalog: &'static SystemLibraryPaths,
    registry: SystemDsoRegistry,
    memory: crate::application::adapters::flat_memory::FlatImageMemory,
}

impl ApplicationLoader {
    /// Build a loader over a fixed catalog, shared registry and shared-flat
    /// memory service.
    pub fn new(
        catalog: &'static SystemLibraryPaths,
        registry: SystemDsoRegistry,
        memory: crate::application::adapters::flat_memory::FlatImageMemory,
    ) -> Self {
        Self {
            catalog,
            registry,
            memory,
        }
    }

    /// The shared-flat memory service the loader links into.
    /// The system DSO registry, for the init-completion path to advance the
    /// pending initialization batch.
    pub fn registry(&self) -> &SystemDsoRegistry {
        &self.registry
    }

    pub fn catalog(&self) -> &'static SystemLibraryPaths {
        self.catalog
    }

    pub fn memory(&self) -> &crate::application::adapters::flat_memory::FlatImageMemory {
        &self.memory
    }

    /// Link a pre-scanned namespace plan under `profile` into `group`.
    ///
    /// The returned [`LinkProduct`] is fully committed and carries the receipt
    /// that owns every raw allocation lease; the caller installs it into the
    /// group and builds the start storage. On any failure the
    /// session rolls back every absorbed allocation and the still-armed registry
    /// permits/leases drop, cancelling the load.
    pub fn link(
        &self,
        plan: NamespaceLoadPlan,
        profile: LoadProfile,
        group: &ThreadGroup,
    ) -> LoadResult<LinkProduct<KernelLinkReceipt>> {
        let mut resolver = NamespaceArtifactResolver::new(plan, self.registry.clone())?;
        let root = resolver.root_artifact()?;
        let linker = DynamicLinker::new(PlatformRelocator);
        let mut memory = self.memory.clone();
        let mut cache = ArchitectureCodeCache::new(CacheRequirements::CURRENT_EXECUTION_CONTEXT);
        let mut publisher = KernelLinkPublisher::new(group.clone());

        let mut building = linker.begin(root, profile, SessionLimits::DEFAULT, &mut memory)?;
        building.close_dependencies(&mut resolver)?;
        let ResolverAuthorities {
            permits,
            leases,
            system_images,
        } = resolver.finish_resolution();
        publisher.import_leases(leases);

        let mut product = building
            .freeze_scopes()?
            .relocate()?
            .seal(&mut cache)?
            .publish(&mut publisher)?;

        // Publish the whole system batch as Initializing and
        // hand the token to the group; ApplicationInitComplete advances it
        // to Ready (or the group's early exit fails it).
        let batch = self.hand_off(permits, &system_images, &mut product)?;
        group
            .install_pending_system_batch(batch)
            .map_err(|_| loader_error())?;
        log_bindings(&product);
        log_lifecycle(&product);

        Ok(product)
    }

    /// Advance every first-loading system candidate to `Initializing` in one
    /// batch and move the receipt's system backings into the registry
    /// Returns the batch token the group holds until the
    /// application reports init completion.
    fn hand_off(
        &self,
        permits: Vec<SystemCandidatePermit>,
        system_images: &[(ArtifactIdentity, DependencyName)],
        product: &mut LinkProduct<KernelLinkReceipt>,
    ) -> LoadResult<SystemInitBatch> {
        // The receipt's raw system allocations are ordered by image id
        // (commit_batch partitions the link map in id order); pair each with
        // its candidate identity for the permit match below. A DSO need not
        // carry `DT_SONAME`, so publication must not use it as identity.
        let allocations = product.publication_mut().take_system_allocations();
        let mut allocations_by_identity: Vec<(ArtifactIdentity, AllocationLease)> = product
            .context()
            .images()
            .iter()
            .filter(|image| image.ownership() == ImageOwnership::SystemCandidate)
            .map(|image| image.descriptor().identity().clone())
            .zip(allocations)
            .collect();
        if permits.len() != allocations_by_identity.len() {
            return Err(loader_error());
        }

        let mut relocated = Vec::new();
        relocated
            .try_reserve(permits.len())
            .map_err(|_| loader_error())?;
        let mut backings = Vec::new();
        backings
            .try_reserve(permits.len())
            .map_err(|_| loader_error())?;
        for candidate in permits {
            let allocation_index = allocations_by_identity
                .iter()
                .position(|(identity, _)| identity == &candidate.identity)
                .ok_or_else(loader_error)?;
            let (_, allocation) = allocations_by_identity.swap_remove(allocation_index);
            let image = product
                .context()
                .images()
                .iter()
                .find(|image| {
                    image.ownership() == ImageOwnership::SystemCandidate
                        && image.descriptor().identity() == &candidate.identity
                })
                .ok_or_else(loader_error)?;
            relocated.push(self.registry.publish_relocated(candidate.permit)?);
            // A system candidate with no destructors has no plan entry; the
            // registry stores an empty plan for it.
            let fini_plan = product
                .lifecycle_plans()
                .system_fini()
                .iter()
                .find(|plan| plan.owner() == image.owner())
                .map(|plan| plan.plan().clone())
                .unwrap_or_default();

            let scc = product
                .lifecycle_plans()
                .sccs()
                .iter()
                .find(|members| members.contains(&image.owner()))
                .ok_or_else(loader_error)?;
            let mut scc_members = Vec::new();
            scc_members
                .try_reserve(scc.len())
                .map_err(|_| loader_error())?;
            for member in scc {
                let member_image = product
                    .context()
                    .images()
                    .iter()
                    .find(|candidate| candidate.owner() == *member)
                    .ok_or_else(loader_error)?;
                if matches!(
                    member_image.ownership(),
                    ImageOwnership::SystemCandidate | ImageOwnership::ExternalReady
                ) {
                    scc_members.push(system_key_for_identity(
                        system_images,
                        member_image.descriptor().identity(),
                    )?);
                }
            }
            if scc_members.is_empty() {
                return Err(loader_error());
            }
            scc_members.sort();
            scc_members.dedup();

            // Retain one lease for every direct outgoing edge to another
            // system SCC. Edges inside this SCC are structural: turning them
            // into ordinary leases would create a self-sustaining cycle.
            let mut dependency_keys = Vec::new();
            for edge in product.context().graph_edges() {
                if edge.requester() != image.owner() || scc.contains(&edge.provider()) {
                    continue;
                }
                let provider = product
                    .context()
                    .images()
                    .iter()
                    .find(|candidate| candidate.owner() == edge.provider())
                    .ok_or_else(loader_error)?;
                if matches!(
                    provider.ownership(),
                    ImageOwnership::SystemCandidate | ImageOwnership::ExternalReady
                ) {
                    dependency_keys.push(system_key_for_identity(
                        system_images,
                        provider.descriptor().identity(),
                    )?);
                }
            }
            dependency_keys.sort();
            dependency_keys.dedup();
            let mut dependencies = Vec::new();
            dependencies
                .try_reserve(dependency_keys.len())
                .map_err(|_| loader_error())?;
            let keep_cached = self
                .catalog
                .resolve_key(&candidate.key)
                .ok_or_else(loader_error)?
                .keep_cached;
            backings.push(SystemCandidateBacking {
                descriptor: image.descriptor_handle(),
                fini_plan,
                allocation,
                dependency_keys,
                dependencies,
                scc_members,
                keep_cached,
            });
        }
        self.registry.publish_relocated_batch(relocated, backings)
    }
}

fn system_key_for_identity(
    system_images: &[(ArtifactIdentity, DependencyName)],
    identity: &ArtifactIdentity,
) -> LoadResult<DependencyName> {
    system_images
        .iter()
        .find(|(candidate, _)| candidate == identity)
        .map(|(_, key)| key.clone())
        .ok_or_else(loader_error)
}

fn loader_error() -> LoadError {
    LoadError::new(LoadErrorKind::Backend, blueos_loader::ErrorContext::None)
}

/// Log the ownership-partitioned lifecycle plans and the frozen SCC snapshot
/// so QEMU checkers can assert the init and
/// group/system fini sequences.
fn log_lifecycle(product: &LinkProduct<KernelLinkReceipt>) {
    let plans = product.lifecycle_plans();
    for (index, entry) in plans.startup().iter().enumerate() {
        log::info!(
            "LIFECYCLE_INIT index={} owner={} address={:#x}",
            index,
            entry.owner().get(),
            entry.function().get()
        );
    }
    for (index, entry) in plans.group_fini().iter().enumerate() {
        log::info!(
            "LIFECYCLE_GROUP_FINI index={} owner={}",
            index,
            entry.owner().get()
        );
    }
    for plan in plans.system_fini() {
        for entry in plan.plan().iter() {
            log::info!("LIFECYCLE_SYSTEM_FINI owner={}", entry.owner().get());
        }
    }
    for edge in product.context().graph_edges() {
        log::info!(
            "LINK_EDGE requester={} provider={}",
            edge.requester().get(),
            edge.provider().get()
        );
    }
    for entry in product.link_map() {
        log::info!(
            "LINK_MAP owner={} soname={} bias={:#x}",
            entry.owner().get(),
            entry
                .soname()
                .map(|s| core::str::from_utf8(s.as_bytes()).unwrap_or("<non-utf8>"))
                .unwrap_or("-"),
            entry.load_bias().get()
        );
    }
    for (group, members) in plans.sccs().iter().enumerate() {
        log::info!(
            "LIFECYCLE_SCC group={} members={:?}",
            group,
            members
                .iter()
                .map(|id| id.get())
                .collect::<alloc::vec::Vec<_>>()
        );
    }
}

/// Log each relocation's frozen scope decision — requester image id, symbol
/// name and winning provider id — for the QEMU
/// checker to assert normalized binding triples.
fn log_bindings(product: &LinkProduct<KernelLinkReceipt>) {
    for binding in product.relocation_bindings() {
        // Local/anonymous dynamic-symbol entries have no externally visible
        // scope decision. Logging them produced hundreds of indistinguishable
        // `name= provider=none` lines for libc and obscured the bindings this
        // record is meant to expose.
        if binding.name().is_empty() {
            continue;
        }
        let name = core::str::from_utf8(binding.name()).unwrap_or("<non-utf8>");
        match binding.provider() {
            Some(provider) => log::info!(
                "SCOPE_BIND requester={} name={} provider={}",
                binding.requester().get(),
                name,
                provider.get()
            ),
            None => log::info!(
                "SCOPE_BIND requester={} name={} provider=none",
                binding.requester().get(),
                name
            ),
        }
    }
}
