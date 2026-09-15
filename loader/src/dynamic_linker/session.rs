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

//! Staged link session typestate and rollback.
//!
//! [`DynamicLinker::begin`] admits the root and absorbs it through the
//! single-image load pipeline, transferring its allocation lease into the
//! session rollback log. [`close_dependencies`](BuildingSession::close_dependencies)
//! drives the bounded BFS closure, de-duplicating by identity before any new
//! allocation. [`freeze_scopes`](BuildingSession::freeze_scopes) consumes the
//! building session into an immutable [`ScopeSet`]. The `relocate`/`seal`
//! transitions preserve the typestate guarantees through publication.

use alloc::{sync::Arc, vec::Vec};

use crate::{
    address::TargetAddress,
    cache::{CacheSyncOutcome, CodeCache},
    dynamic_linker::{
        graph::{DependencyGraph, DiscoveryItem, DiscoveryQueue},
        lifecycle::{self, FiniPlan, InitPlan, LifecycleImage, LifecyclePlans},
        publish::{
            self, CommittedImage, CommittingLinkProduct, LinkContext, LinkMapImage, LinkProduct,
            LinkPublisher, PreparedLinkManifest,
        },
        relocate::{self, ProviderRegion, RelocationImage, RelocationPolicy, RelocationSource},
        scope::RelocationBinding,
        ArtifactIdentity, ArtifactResolver, ArtifactRole, DependencyName, DependencyRequest,
        DependencyRequester, DependencyResolution, ImageId, ImageOwnership,
        PublishedImageDescriptor, PublishedRegion, ResolvedArtifact, RuntimeImageMetadata,
        RuntimeImageState, ScopeSet, SymbolTable,
    },
    elf::LoadSegmentInfo,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::{
        ElfType, LoadLimits, LoadPolicy, LoadProfile, LoadRequest, SessionLimits,
        DYNAMIC_LINK_LOAD_POLICY,
    },
    image::{
        absorb_into_session, AppliedProtectionSet, ImageLoader, LoadedRegion,
        PreparedProtectionPlan, ProtectionBatch, SealPlan, SealedState,
    },
    memory::{AllocationRollbackLog, ImageMemory, ImageProtectionMemory, SessionAllocation},
    reader::ElfReader,
    relocation::ArchRelocator,
};

/// Resource usage that must be accumulated across a link session to enforce
/// limits spanning more than one image or lookup.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct SessionUsage {
    symbol_lookups: u64,
    image_bytes: u64,
    runtime_metadata_bytes: u64,
}

impl SessionUsage {
    #[inline]
    pub(crate) fn record_image(
        &mut self,
        image_bytes: u64,
        metadata_bytes: u64,
        limits: &SessionLimits,
    ) -> LoadResult<()> {
        let total_image_bytes = self
            .image_bytes
            .checked_add(image_bytes)
            .ok_or_else(session_overflow)?;
        let total_metadata_bytes = self
            .runtime_metadata_bytes
            .checked_add(metadata_bytes)
            .ok_or_else(session_overflow)?;
        limits.check_total_image_bytes(total_image_bytes)?;
        limits.check_total_runtime_metadata_bytes(total_metadata_bytes)?;
        self.image_bytes = total_image_bytes;
        self.runtime_metadata_bytes = total_metadata_bytes;
        Ok(())
    }

    #[inline]
    pub(crate) fn record_symbol_lookup(&mut self, limits: &SessionLimits) -> LoadResult<()> {
        let next = self
            .symbol_lookups
            .checked_add(1)
            .ok_or_else(session_overflow)?;
        limits.check_symbol_lookups(next)?;
        self.symbol_lookups = next;
        Ok(())
    }

    /// Charge the relocation-binding snapshot (name copies plus the
    /// fixed per-binding overhead) against the runtime metadata budget.
    #[inline]
    pub(crate) fn record_relocation_bindings(
        &mut self,
        bytes: u64,
        limits: &SessionLimits,
    ) -> LoadResult<()> {
        let total = self
            .runtime_metadata_bytes
            .checked_add(bytes)
            .ok_or_else(session_overflow)?;
        limits.check_total_runtime_metadata_bytes(total)?;
        self.runtime_metadata_bytes = total;
        Ok(())
    }
}

/// One image admitted into the session, parameterized by its pipeline state.
///
/// `allocation` is a copyable descriptor plus an unforgeable rollback slot: it
/// can select the image for reads/writes but has no authority to abort or
/// commit the allocation. The unique lease lives only in the session rollback
/// log.
pub(crate) struct SessionImage<S> {
    image_id: ImageId,
    allocation: SessionAllocation,
    state: S,
}

/// One Ready system image imported from the registry instead of loaded.
///
/// It joins the dependency graph, the symbol scopes, the link map and the
/// committed context, but is never allocated, relocated, sealed or
/// re-initialized here — its unique lease lives in the system registry, not in
/// this session's rollback log. The owned descriptor supplies the export
/// surface and published regions the later stages read from.
pub(crate) struct ImportedImage {
    image_id: ImageId,
    descriptor: Arc<PublishedImageDescriptor>,
}

impl ImportedImage {
    #[inline]
    pub(crate) fn descriptor(&self) -> &PublishedImageDescriptor {
        self.descriptor.as_ref()
    }
}

/// Immutable session state while dependencies are being discovered.
pub struct BuildingState {
    images: Vec<SessionImage<RuntimeImageState>>,
    imported: Vec<ImportedImage>,
    discovery: DiscoveryQueue,
    closed: bool,
    poisoned: bool,
}

/// Immutable session state once scopes are frozen.
pub struct ScopedState {
    images: Vec<SessionImage<RuntimeImageState>>,
    imported: Vec<ImportedImage>,
    scopes: ScopeSet,
}

/// Owned runtime state after session-wide relocation. Relocation only
/// rewrites memory; the decoded metadata, load regions and segments are
/// unchanged, so this newtypes the decoded state to make a second relocation
/// unrepresentable.
pub struct RelocatedImageState(RuntimeImageState);

impl RelocatedImageState {
    #[inline]
    pub(crate) fn regions(&self) -> &[LoadedRegion] {
        self.0.regions()
    }

    #[inline]
    pub(crate) fn load_segments(&self) -> &[LoadSegmentInfo] {
        self.0.load_segments()
    }

    #[inline]
    pub(crate) const fn metadata(&self) -> &RuntimeImageMetadata {
        self.0.metadata()
    }

    #[inline]
    pub(crate) const fn load_bias(&self) -> TargetAddress {
        self.0.load_bias()
    }

    #[inline]
    pub(crate) const fn runtime_entry(&self) -> TargetAddress {
        self.0.runtime_entry()
    }
}

/// Immutable session state once every image is relocated.
pub struct RelocatedState {
    images: Vec<SessionImage<RelocatedImageState>>,
    imported: Vec<ImportedImage>,
    /// Recorded scope decision for each relocation.
    bindings: Vec<RelocationBinding>,
}

/// Per-image state after cache synchronization and memory protection.
pub struct SealedImageState {
    runtime: RuntimeImageState,
    sealed: SealedState,
}

impl SealedImageState {
    #[inline]
    pub(crate) fn regions(&self) -> &[LoadedRegion] {
        self.runtime.regions()
    }

    #[inline]
    pub(crate) fn load_segments(&self) -> &[LoadSegmentInfo] {
        self.runtime.load_segments()
    }

    #[inline]
    pub(crate) const fn metadata(&self) -> &RuntimeImageMetadata {
        self.runtime.metadata()
    }

    #[inline]
    pub(crate) const fn load_bias(&self) -> TargetAddress {
        self.runtime.load_bias()
    }

    #[inline]
    pub(crate) const fn runtime_entry(&self) -> TargetAddress {
        self.runtime.runtime_entry()
    }
}

/// Immutable session state once every image has crossed the cache and
/// protection boundary.
pub struct SealedSessionState {
    images: Vec<SessionImage<SealedImageState>>,
    imported: Vec<ImportedImage>,
    /// Recorded scope decision for each relocation.
    bindings: Vec<RelocationBinding>,
}

/// The rollback authority for a live session: it owns the memory backend it
/// aborts against and the unique allocation leases absorbed so far.
///
/// This is separated from [`LinkSession`] so the session itself can move fields
/// in consuming transitions without Rust's move-out-of-`Drop` restriction, while
/// still guaranteeing reverse-order abort on any early exit.
struct RollbackGuard<'a, M: ImageMemory + ?Sized> {
    memory: &'a mut M,
    log: AllocationRollbackLog,
}

impl<M: ImageMemory + ?Sized> Drop for RollbackGuard<'_, M> {
    fn drop(&mut self) {
        self.log.abort_all(&mut *self.memory);
    }
}

/// A staged, multi-image link session.
///
/// `S` is one of [`BuildingState`], [`ScopedState`] or [`RelocatedState`]
/// (and, in , a sealed state). The session owns the dependency graph, the
/// rollback log and the cross-image resource usage; the trusted [`LoadProfile`],
/// [`LoadPolicy`] and the single [`ArchRelocator`] are carried so every image
/// reuses the same profile and relocation semantics without re-deriving them.
pub struct LinkSession<'a, M: ImageMemory + ?Sized, S, A> {
    rollback: RollbackGuard<'a, M>,
    graph: DependencyGraph,
    limits: SessionLimits,
    usage: SessionUsage,
    profile: LoadProfile,
    policy: LoadPolicy,
    arch: A,
    state: S,
}

pub type BuildingSession<'a, M, A> = LinkSession<'a, M, BuildingState, A>;
pub type ScopedSession<'a, M, A> = LinkSession<'a, M, ScopedState, A>;
pub type RelocatedSession<'a, M, A> = LinkSession<'a, M, RelocatedState, A>;
pub type SealedSession<'a, M, A> = LinkSession<'a, M, SealedSessionState, A>;

/// Multi-image linker configured with a trusted profile, a session budget and
/// the single [`ArchRelocator`] used by every image in the link.
pub struct DynamicLinker<A> {
    arch: A,
    policy: LoadPolicy,
}

impl<A: ArchRelocator> DynamicLinker<A> {
    pub fn new(arch: A) -> Self {
        Self {
            arch,
            policy: DYNAMIC_LINK_LOAD_POLICY,
        }
    }

    /// Run a complete link in one call: admit the root, close the dependency
    /// closure, freeze scopes, relocate, seal, and publish.
    ///
    /// This is the convenience wrapper over the staged API; it consumes the
    /// linker because the single [`ArchRelocator`] is moved through every
    /// session transition. The `memory` backend must support protection
    /// (`ImageProtectionMemory`) so the session can reach the seal stage.
    pub fn link<R, Resolver, Memory, Cache, Publisher>(
        self,
        root: ResolvedArtifact<R>,
        profile: LoadProfile,
        limits: SessionLimits,
        resolver: &mut Resolver,
        memory: &mut Memory,
        cache: &mut Cache,
        publisher: &mut Publisher,
    ) -> LoadResult<LinkProduct<Publisher::Receipt>>
    where
        R: ElfReader,
        Resolver: ArtifactResolver,
        Memory: ImageProtectionMemory + ?Sized,
        Cache: CodeCache + ?Sized,
        Publisher: LinkPublisher,
    {
        let mut building = self.begin(root, profile, limits, memory)?;
        building.close_dependencies(resolver)?;
        building
            .freeze_scopes()?
            .relocate()?
            .seal(cache)?
            .publish(publisher)
    }

    /// Admit the root and open a building session.
    ///
    /// The root is always an [`ArtifactRole::ExecutableRoot`]; its reader is
    /// consumed by the image pipeline and the resulting allocation lease is absorbed
    /// into the session rollback log before the session is returned.
    pub fn begin<R, Memory>(
        self,
        root: ResolvedArtifact<R>,
        profile: LoadProfile,
        limits: SessionLimits,
        memory: &mut Memory,
    ) -> LoadResult<BuildingSession<'_, Memory, A>>
    where
        R: ElfReader,
        Memory: ImageMemory + ?Sized,
    {
        if self.arch.machine() != profile.machine() || self.arch.class() != profile.class() {
            return Err(
                LoadError::new(LoadErrorKind::UnsupportedByProfile, ErrorContext::None)
                    .at_stage(LoadStage::Beginning),
            );
        }
        // The link root is always an allocated `ET_DYN` image owned by this
        // session. A fixed `ET_EXEC` stays on the single-image path,
        // and a system-candidate root would let an application reserve system
        // symbol space it cannot own.
        if profile.r#type() != ElfType::Dyn {
            return Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::HeaderField {
                    field: crate::error::HeaderField::Type,
                    value: u64::from(profile.r#type()),
                },
            )
            .at_stage(LoadStage::Beginning));
        }
        if root.ownership() != ImageOwnership::SessionPrivate {
            return Err(
                LoadError::new(LoadErrorKind::UnsupportedByProfile, ErrorContext::None)
                    .at_stage(LoadStage::Beginning),
            );
        }

        let mut guard = RollbackGuard {
            memory,
            log: AllocationRollbackLog::new(),
        };
        let mut graph = DependencyGraph::new(limits);
        let mut usage = SessionUsage::default();

        let (artifact, ownership, reader) = root.into_parts();
        let (allocation, mut runtime) = load_runtime(
            reader,
            profile,
            ArtifactRole::ExecutableRoot,
            self.policy,
            limits.per_image(),
            &mut guard.log,
            &mut *guard.memory,
        )?;

        let soname = runtime.take_soname();
        let metadata_bytes = session_image_metadata_bytes(&runtime, &artifact, soname.as_ref())?;
        let root_id = graph.insert_root(artifact, soname, ownership)?;
        validate_session_symbol_names(&runtime, &limits)?;
        usage
            .record_image(allocation.allocation().len(), metadata_bytes, &limits)
            .map_err(|error| error.at_stage(LoadStage::Beginning))?;

        let mut images = Vec::new();
        images
            .try_reserve(1)
            .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        images.push(SessionImage {
            image_id: root_id,
            allocation,
            state: runtime,
        });

        let mut discovery = DiscoveryQueue::new(limits);
        enqueue_dependencies(
            &mut discovery,
            root_id,
            images[0].state.metadata().needed(),
            &limits,
            LoadStage::Beginning,
        )?;

        Ok(LinkSession {
            rollback: guard,
            graph,
            limits,
            usage,
            profile,
            policy: self.policy,
            arch: self.arch,
            state: BuildingState {
                images,
                imported: Vec::new(),
                discovery,
                closed: false,
                poisoned: false,
            },
        })
    }
}

impl<'a, M: ImageMemory + ?Sized, A: ArchRelocator> BuildingSession<'a, M, A> {
    /// Drive the bounded BFS closure until the discovery queue is empty.
    ///
    /// Each resolved dependency is de-duplicated by identity *before* it is
    /// loaded; an already-loaded provider only records an extra edge. A new
    /// artifact runs the load pipeline, is absorbed into the session
    /// rollback log, and its own `DT_NEEDED` are enqueued in encounter order.
    pub fn close_dependencies<Resolver: ArtifactResolver>(
        &mut self,
        resolver: &mut Resolver,
    ) -> LoadResult<()> {
        if self.state.poisoned {
            return Err(session_error(LoadErrorKind::BadElf, ErrorContext::None)
                .at_stage(LoadStage::Discover));
        }
        if self.state.closed {
            return Ok(());
        }

        let result = self.close_dependencies_inner(resolver);
        if result.is_err() {
            self.state.poisoned = true;
        }
        result
    }

    fn close_dependencies_inner<Resolver: ArtifactResolver>(
        &mut self,
        resolver: &mut Resolver,
    ) -> LoadResult<()> {
        while let Some(item) = self.state.discovery.pop() {
            let requester = item.requester();
            let resolved = {
                let requester_node = self
                    .graph
                    .node(requester)
                    .ok_or_else(|| session_error(LoadErrorKind::BadElf, ErrorContext::None))?;
                let needed = needed_for(&self.state.images, requester, item.needed_index())?;
                // The resolver sees the full requester context: the
                // session-local image id, its identity and its ownership — so
                // package/system resolution can be decided per requester.
                let request = DependencyRequest::new(
                    DependencyRequester::new(
                        requester,
                        requester_node.artifact(),
                        requester_node.ownership(),
                    ),
                    needed,
                );
                resolver.resolve(&request).map_err(|error| {
                    error
                        .at_stage(LoadStage::Discover)
                        .with_context(ErrorContext::Dependency {
                            requester: requester.get(),
                            needed: needed.as_bytes().into(),
                        })
                })?
            };

            match resolved {
                DependencyResolution::Load(artifact) => {
                    let (identity, ownership, reader) = artifact.into_parts();

                    // Identity de-duplication happens before any allocation
                    // so repeated requests reuse the same graph node.
                    if let Some(existing) = self.graph.find_identity(&identity) {
                        self.graph
                            .link_existing(requester, existing, item.needed_index())
                            .map_err(|error| error.at_stage(LoadStage::Discover))?;
                        continue;
                    }

                    let (allocation, mut runtime) = load_runtime(
                        reader,
                        self.profile,
                        ArtifactRole::SharedObject,
                        self.policy,
                        self.limits.per_image(),
                        &mut self.rollback.log,
                        &mut *self.rollback.memory,
                    )
                    .map_err(|error| error.at_stage(LoadStage::Discover))?;

                    let soname = runtime.take_soname();
                    let metadata_bytes =
                        session_image_metadata_bytes(&runtime, &identity, soname.as_ref())?;
                    let needed = needed_for(&self.state.images, requester, item.needed_index())?;
                    let provider = self
                        .graph
                        .insert_dependency(
                            requester,
                            needed,
                            item.needed_index(),
                            identity,
                            soname,
                            ownership,
                        )
                        .map_err(|error| error.at_stage(LoadStage::Discover))?;

                    validate_session_symbol_names(&runtime, &self.limits)
                        .map_err(|error| error.at_stage(LoadStage::Discover))?;
                    self.usage
                        .record_image(allocation.allocation().len(), metadata_bytes, &self.limits)
                        .map_err(|error| error.at_stage(LoadStage::Discover))?;

                    enqueue_dependencies(
                        &mut self.state.discovery,
                        provider,
                        runtime.metadata().needed(),
                        &self.limits,
                        LoadStage::Discover,
                    )?;

                    self.state.images.try_reserve(1).map_err(|_| {
                        LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
                            .at_stage(LoadStage::Discover)
                    })?;
                    self.state.images.push(SessionImage {
                        image_id: provider,
                        allocation,
                        state: runtime,
                    });
                }

                DependencyResolution::Import(imported) => {
                    let descriptor = imported.into_descriptor();

                    // An imported Ready image is joined to the graph and scopes
                    // without a fresh allocation, relocation, seal, or init.
                    // It never contributes a `DT_NEEDED` of its own
                    // here: its dependency closure was fixed by the link that
                    // first published it.
                    //
                    // Identity de-duplication mirrors the Load path: an
                    // already-present imported provider only records an
                    // extra edge, never a second `ImportedImage` entry.
                    let identity = descriptor.identity().try_clone()?;
                    if let Some(existing) = self.graph.find_identity(&identity) {
                        self.graph
                            .link_existing(requester, existing, item.needed_index())
                            .map_err(|error| error.at_stage(LoadStage::Discover))?;
                        continue;
                    }

                    let needed = needed_for(&self.state.images, requester, item.needed_index())?;
                    let soname = descriptor
                        .soname()
                        .map(DependencyName::try_clone)
                        .transpose()?;
                    let provider = self
                        .graph
                        .insert_dependency(
                            requester,
                            needed,
                            item.needed_index(),
                            identity,
                            soname,
                            ImageOwnership::ExternalReady,
                        )
                        .map_err(|error| error.at_stage(LoadStage::Discover))?;

                    let metadata_bytes = imported_metadata_bytes(&descriptor)?;
                    self.usage
                        .record_image(0, metadata_bytes, &self.limits)
                        .map_err(|error| error.at_stage(LoadStage::Discover))?;

                    self.state.imported.try_reserve(1).map_err(|_| {
                        LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
                            .at_stage(LoadStage::Discover)
                    })?;
                    self.state.imported.push(ImportedImage {
                        image_id: provider,
                        descriptor,
                    });
                }
            }
        }

        self.state.closed = true;
        Ok(())
    }

    /// Freeze the closed dependency graph into an immutable [`ScopeSet`].
    ///
    /// Consumes the building session; on any error the session is dropped and
    /// every absorbed allocation is aborted in reverse creation order.
    pub fn freeze_scopes(self) -> LoadResult<ScopedSession<'a, M, A>> {
        let LinkSession {
            rollback,
            graph,
            limits,
            usage,
            profile,
            policy,
            arch,
            state,
        } = self;
        let BuildingState {
            images,
            imported,
            discovery: _,
            closed,
            poisoned,
        } = state;

        if !closed || poisoned {
            return Err(LoadError::new(LoadErrorKind::BadElf, ErrorContext::None)
                .at_stage(LoadStage::Scope));
        }

        // The symbol table array is image-id indexed and must include imported
        // Ready images at their graph-assigned positions, so a lookup
        // into an imported provider resolves against its retained export table.
        let mut symbols = Vec::new();
        symbols
            .try_reserve_exact(images.len() + imported.len())
            .map_err(|_| scope_session_oom())?;
        let mut tables: Vec<Option<&SymbolTable>> = Vec::new();
        tables
            .try_reserve_exact(images.len() + imported.len())
            .map_err(|_| scope_session_oom())?;
        tables.resize_with(images.len() + imported.len(), || None);
        for image in &images {
            tables[image.image_id.get() as usize] = Some(image.state.metadata().symbols());
        }
        for imported in &imported {
            tables[imported.image_id.get() as usize] = Some(imported.descriptor().exports());
        }
        for table in tables {
            symbols.push(table.ok_or_else(|| {
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None).at_stage(LoadStage::Scope)
            })?);
        }
        let scopes = ScopeSet::freeze(&graph).map_err(|error| error.at_stage(LoadStage::Scope))?;

        Ok(LinkSession {
            rollback,
            graph,
            limits,
            usage,
            profile,
            policy,
            arch,
            state: ScopedState {
                images,
                imported,
                scopes,
            },
        })
    }
}

impl<'a, M: ImageMemory + ?Sized, A: ArchRelocator> ScopedSession<'a, M, A> {
    /// Run the session-wide relocation.
    ///
    /// Consumes the scoped session; every decoded relocation record is
    /// preflighted and applied against the frozen scopes. On any error the
    /// session is dropped and all absorbed allocations aborted.
    pub fn relocate(mut self) -> LoadResult<RelocatedSession<'a, M, A>> {
        let image_count = self.state.images.len();
        let total_images = image_count + self.state.imported.len();
        let mut relocated_images = Vec::new();
        relocated_images
            .try_reserve_exact(image_count)
            .map_err(|_| link_relocation_oom())?;

        // Both arrays are image-id indexed over every admitted image — loaded
        // and imported — because relocation resolves a symbol's owner
        // id back into them. `symbols` supplies each imported provider's
        // retained export table; `relocation_images` is `None` at an imported
        // id (an imported image contributes no relocation records and is never
        // rewritten), while `apply` indexes it by owner id.
        let mut symbol_slots: Vec<Option<&SymbolTable>> = Vec::new();
        symbol_slots
            .try_reserve_exact(total_images)
            .map_err(|_| link_relocation_oom())?;
        symbol_slots.resize_with(total_images, || None);
        let mut relocation_slots: Vec<Option<RelocationImage<'_>>> = Vec::new();
        relocation_slots
            .try_reserve_exact(total_images)
            .map_err(|_| link_relocation_oom())?;
        relocation_slots.resize_with(total_images, || None);
        for image in &self.state.images {
            symbol_slots[image.image_id.get() as usize] = Some(image.state.metadata().symbols());
            relocation_slots[image.image_id.get() as usize] = Some(RelocationImage::new(
                image.image_id,
                image.allocation,
                image.state.regions(),
                image.state.load_segments(),
                image.state.metadata(),
                image.state.load_bias(),
            ));
        }
        for imported in &self.state.imported {
            symbol_slots[imported.image_id.get() as usize] = Some(imported.descriptor().exports());
        }
        let mut symbols = Vec::new();
        symbols
            .try_reserve_exact(total_images)
            .map_err(|_| link_relocation_oom())?;
        for slot in symbol_slots {
            symbols.push(slot.ok_or_else(|| {
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None)
                    .at_stage(LoadStage::LinkRelocate)
            })?);
        }
        let mut relocation_images = Vec::new();
        relocation_images
            .try_reserve_exact(total_images)
            .map_err(|_| link_relocation_oom())?;
        relocation_images.extend(relocation_slots);

        // The provider-region array is image-id indexed over every admitted
        // image, loaded and imported, so a symbol resolved into an
        // imported provider is range-checked against the same facts a fresh
        // load would have produced.
        let mut provider_regions = Vec::new();
        provider_regions
            .try_reserve_exact(total_images)
            .map_err(|_| link_relocation_oom())?;
        provider_regions.resize_with(total_images, Vec::new);
        for image in &self.state.images {
            let regions = image
                .state
                .load_segments()
                .iter()
                .zip(image.state.regions().iter())
                .map(|(segment, region)| {
                    ProviderRegion::new(segment.permissions(), region.runtime_range())
                })
                .collect();
            provider_regions[image.image_id.get() as usize] = regions;
        }
        for imported in &self.state.imported {
            let regions = imported
                .descriptor()
                .regions()
                .iter()
                .map(|region| ProviderRegion::new(region.permissions(), region.runtime_range()))
                .collect();
            provider_regions[imported.image_id.get() as usize] = regions;
        }

        let policy = RelocationPolicy::for_profile(&self.profile);
        let operations = relocate::run(
            &self.arch,
            &symbols,
            &relocation_images,
            &provider_regions,
            &self.state.scopes,
            &self.profile,
            &policy,
            &self.limits,
            &mut self.usage,
            &mut *self.rollback.memory,
            &mut self.rollback.log,
        )
        .map_err(|error| error.at_stage(LoadStage::LinkRelocate))?;

        // Record every relocation's scope decision:
        // requester, symbol name and winning provider — into the published
        // snapshot before any state is rewrapped.
        let bindings = record_bindings(&operations, &symbols, &self.limits, &mut self.usage)?;

        drop(relocation_images);
        drop(symbols);

        let ScopedState {
            images,
            imported,
            scopes: _,
        } = self.state;
        // Rewrap the decoded state so a second relocation is unrepresentable.
        // Frozen scopes have served their only purpose and are dropped here.
        for image in images {
            relocated_images.push(SessionImage {
                image_id: image.image_id,
                allocation: image.allocation,
                state: RelocatedImageState(image.state),
            });
        }
        Ok(LinkSession {
            rollback: self.rollback,
            graph: self.graph,
            limits: self.limits,
            usage: self.usage,
            profile: self.profile,
            policy: self.policy,
            arch: self.arch,
            state: RelocatedState {
                images: relocated_images,
                imported,
                bindings,
            },
        })
    }
}

impl<'a, M: ImageProtectionMemory + ?Sized, A: ArchRelocator> RelocatedSession<'a, M, A> {
    /// Complete the session-wide cache and protection boundary.
    ///
    /// Every logical seal plan, backend protection plan and executable range
    /// is prepared before the first cache/protection mutation. Publication is
    /// available only on the returned [`SealedSession`].
    pub fn seal<C: CodeCache + ?Sized>(
        mut self,
        cache: &mut C,
    ) -> LoadResult<SealedSession<'a, M, A>> {
        let image_count = self.state.images.len();
        let total_executable_ranges =
            self.state.images.iter().try_fold(0usize, |total, image| {
                let count = image
                    .state
                    .load_segments()
                    .iter()
                    .filter(|segment| {
                        segment
                            .permissions()
                            .contains(crate::MemoryPermissions::EXECUTE)
                            && segment.memory_size() != 0
                    })
                    .count();
                total.checked_add(count).ok_or_else(|| {
                    session_error(LoadErrorKind::IntegerOverflow, ErrorContext::None)
                        .at_stage(LoadStage::LinkSeal)
                })
            })?;

        let mut executable_ranges = Vec::new();
        executable_ranges
            .try_reserve_exact(total_executable_ranges)
            .map_err(|_| link_seal_oom())?;
        let mut prepared_seals = Vec::new();
        prepared_seals
            .try_reserve_exact(image_count)
            .map_err(|_| link_seal_oom())?;
        let mut sealed_images = Vec::new();
        sealed_images
            .try_reserve_exact(image_count)
            .map_err(|_| link_seal_oom())?;
        let mut output = Vec::new();
        output
            .try_reserve_exact(image_count)
            .map_err(|_| link_seal_oom())?;

        for image in &self.state.images {
            let runtime = &image.state.0;
            let allocation = image.allocation.allocation();
            let seal_plan = SealPlan::build(
                &allocation,
                runtime.load_bias(),
                self.profile.class(),
                runtime.load_segments(),
                runtime.regions(),
                runtime.relro(),
                runtime.stack(),
                runtime.metadata().relocations().records(),
            )
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
            let prepared = PreparedProtectionPlan::prepare_for_allocation(
                &*self.rollback.memory,
                &allocation,
                &seal_plan,
            )
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;

            let executable_count = runtime
                .load_segments()
                .iter()
                .filter(|segment| {
                    segment
                        .permissions()
                        .contains(crate::MemoryPermissions::EXECUTE)
                        && segment.memory_size() != 0
                })
                .count();
            let mut image_executable_ranges = Vec::new();
            image_executable_ranges
                .try_reserve_exact(executable_count)
                .map_err(|_| link_seal_oom())?;
            for (segment, region) in runtime.load_segments().iter().zip(runtime.regions().iter()) {
                if segment
                    .permissions()
                    .contains(crate::MemoryPermissions::EXECUTE)
                    && !region.runtime_range().is_empty()
                {
                    image_executable_ranges.push(region.runtime_range());
                    executable_ranges.push(region.runtime_range());
                }
            }
            prepared_seals.push((seal_plan, prepared, image_executable_ranges));
        }

        let requirements = cache.requirements();
        let prepared_cache = cache
            .prepare(&executable_ranges)
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        requirements
            .validate_prepared(&executable_ranges, &prepared_cache)
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        let cache_scope = prepared_cache.scope();
        let cache_maintenance = prepared_cache.maintenance();
        let cache_sync = cache
            .synchronize(prepared_cache)
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        cache_sync
            .validate_completion(&executable_ranges, cache_scope, cache_maintenance)
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        for (image, (seal_plan, prepared, image_executable_ranges)) in
            self.state.images.iter().zip(prepared_seals.into_iter())
        {
            let allocation = image.allocation.allocation();
            let mut protection_records = prepared.into_ranges();
            self.rollback
                .log
                .mark_protection_modified(image.allocation)
                .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
            self.rollback
                .memory
                .apply_protection(&allocation, ProtectionBatch::new(&mut protection_records))
                .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
            let image_cache_sync = CacheSyncOutcome::from_synchronized_ranges(
                image_executable_ranges,
                cache_scope,
                cache_maintenance,
            );
            sealed_images.push(SealedState::new(
                image.state.load_bias(),
                image.state.runtime_entry(),
                image.state.0.canonical_runtime_entry(),
                image_cache_sync,
                seal_plan,
                AppliedProtectionSet::new(protection_records),
            ));
        }

        let RelocatedState {
            images,
            imported,
            bindings,
        } = self.state;
        let mut images = images.into_iter();
        let mut sealed_states = sealed_images.into_iter();
        while let (Some(image), Some(sealed)) = (images.next(), sealed_states.next()) {
            output.push(SessionImage {
                image_id: image.image_id,
                allocation: image.allocation,
                state: SealedImageState {
                    runtime: image.state.0,
                    sealed,
                },
            });
        }

        Ok(LinkSession {
            rollback: self.rollback,
            graph: self.graph,
            limits: self.limits,
            usage: self.usage,
            profile: self.profile,
            policy: self.policy,
            arch: self.arch,
            state: SealedSessionState {
                images: output,
                imported,
                bindings,
            },
        })
    }
}

impl<M: ImageMemory + ?Sized, A: ArchRelocator> SealedSession<'_, M, A> {
    /// Build the dependency-first init and reverse fini plans.
    ///
    /// Reads the post-relocation init/fini array words back through the
    /// session memory backend and validates each non-sentinel function target
    /// against its owner's executable region (and Thumb bit on ARM). The plans
    /// only *name* targets — nothing here calls a constructor.
    pub fn build_lifecycle_plans(&self) -> LoadResult<LifecyclePlans> {
        let mut images = Vec::new();
        images
            .try_reserve_exact(self.state.images.len())
            .map_err(|_| link_seal_oom())?;
        for image in &self.state.images {
            images.push(LifecycleImage::new(
                image.image_id,
                image.allocation,
                image.state.regions(),
                image.state.load_segments(),
                image.state.metadata().lifecycle(),
                image.state.load_bias(),
            ));
        }
        lifecycle::build(&self.graph, &images, &self.profile, &*self.rollback.memory)
    }

    /// Build the prepared link manifest (link map + root entry) for atomic
    /// publication.
    ///
    /// Emits one [`LinkMapEntry`] per relocated image in image-id order and
    /// uses the root's runtime entry computed during mapping. The
    /// result holds no lease: it is the pure description the host publisher
    /// validates in `prepare_batch` before the committed snapshot is swapped.
    pub fn prepare_link_manifest(&self) -> LoadResult<PreparedLinkManifest> {
        let total = self.state.images.len() + self.state.imported.len();
        // Image-id indexed: the root and every loaded image contribute a
        // `Loaded` entry, and every imported Ready image a `Imported` entry at
        // its graph-assigned id, so the link map stays in stable id order even
        // when discovery interleaves loads and imports.
        let mut slots: Vec<Option<LinkMapImage>> = Vec::new();
        slots
            .try_reserve_exact(total)
            .map_err(|_| link_seal_oom())?;
        slots.resize_with(total, || None);
        for image in &self.state.images {
            slots[image.image_id.get() as usize] = Some(LinkMapImage::loaded(
                image.image_id,
                image.state.load_bias(),
                image.state.runtime_entry(),
            ));
        }
        for imported in &self.state.imported {
            slots[imported.image_id.get() as usize] = Some(LinkMapImage::imported(
                imported.image_id,
                imported.descriptor().load_bias(),
            ));
        }
        let mut images = Vec::new();
        images
            .try_reserve_exact(total)
            .map_err(|_| link_seal_oom())?;
        for slot in slots {
            images.push(slot.ok_or_else(|| {
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None)
                    .at_stage(LoadStage::LinkSeal)
            })?);
        }
        publish::build_manifest(&self.graph, &images)
    }

    /// Atomically publish the link product.
    ///
    /// Builds the lifecycle plans and the prepared manifest, lets the publisher
    /// complete every fallible check without mutating the visible snapshot,
    /// then moves the unique allocation leases out of the session rollback log
    /// into the publisher's committed owner in one infallible commit. On any
    /// `prepare_batch` failure the session drops and aborts every absorbed
    /// allocation; after a successful commit the rollback log is empty and the
    /// publisher's `Receipt` is the long-term owner of the committed images.
    pub fn publish<P: LinkPublisher>(
        self,
        publisher: &mut P,
    ) -> LoadResult<LinkProduct<P::Receipt>> {
        let plans = self.build_lifecycle_plans()?;
        let manifest = self.prepare_link_manifest()?;

        // One committed image per id: link-map facts plus the backing
        // allocation, in image-id order. Imported Ready images join the
        // committed context at their graph-assigned ids so their retained
        // export surface stays resolvable after publication; they
        // contribute no lease here — their unique lease lives in the registry.
        let total = self.state.images.len() + self.state.imported.len();
        // Drain the unique leases in creation order (== image-id order of the
        // loaded images only).
        let mut leases = Vec::new();
        leases
            .try_reserve_exact(self.rollback.log.len())
            .map_err(|_| publish_oom())?;

        let LinkSession {
            mut rollback,
            graph,
            limits: _,
            usage: _,
            profile: _,
            policy: _,
            arch: _,
            state,
        } = self;
        let SealedSessionState {
            images,
            imported,
            bindings,
        } = state;

        let mut slots: Vec<Option<CommittedImage>> = Vec::new();
        slots.try_reserve_exact(total).map_err(|_| publish_oom())?;
        slots.resize_with(total, || None);

        for image in images {
            let node = graph.node(image.image_id).ok_or_else(|| {
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None)
                    .at_stage(LoadStage::Publish)
            })?;
            let SealedImageState { runtime, sealed: _ } = image.state;
            let (regions, load_segments, load_bias, program_headers, symbols) =
                runtime.into_publish_parts();
            let ownership = node.ownership();
            let descriptor = Arc::new(
                PublishedImageDescriptor::from_node_and_state(
                    node,
                    regions,
                    load_segments,
                    load_bias,
                    program_headers,
                    symbols,
                )
                .map_err(|error| error.at_stage(LoadStage::Publish))?,
            );
            slots[image.image_id.get() as usize] =
                Some(CommittedImage::new(image.image_id, ownership, descriptor));
        }
        for imported in imported {
            let image_id = imported.image_id;
            slots[image_id.get() as usize] = Some(CommittedImage::new(
                image_id,
                ImageOwnership::ExternalReady,
                imported.descriptor,
            ));
        }

        let mut committed = Vec::new();
        committed
            .try_reserve_exact(total)
            .map_err(|_| publish_oom())?;
        for slot in slots {
            committed.push(slot.ok_or_else(|| {
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None)
                    .at_stage(LoadStage::Publish)
            })?);
        }

        let context = LinkContext::new(graph, committed);
        let prepared = publisher
            .prepare_batch(&manifest)
            .map_err(|error| error.at_stage(LoadStage::Publish))?;
        let (entry, link_map) = manifest.into_parts();
        rollback.log.drain_leases_into(&mut leases);
        let product = CommittingLinkProduct::new(leases);

        // SAFETY: `prepared` and `product` were produced by this same live
        // session; every fallible check completed before the leases moved.
        let receipt = unsafe { publisher.commit_batch(prepared, product) };

        Ok(LinkProduct::new(
            context, entry, plans, link_map, bindings, receipt,
        ))
    }
}

/// Run the single-image – pipeline on `reader` under `profile`/`role`, then
/// transfer the resulting allocation lease into the session rollback log and
/// return the decoded runtime state.
fn load_runtime<R, Memory>(
    reader: R,
    profile: LoadProfile,
    role: ArtifactRole,
    policy: LoadPolicy,
    limits: &LoadLimits,
    rollback: &mut AllocationRollbackLog,
    memory: &mut Memory,
) -> LoadResult<(SessionAllocation, RuntimeImageState)>
where
    R: ElfReader,
    Memory: ImageMemory + ?Sized,
{
    let request = LoadRequest::new(profile, *limits);
    let decoded = ImageLoader::new(reader, request)
        .admit()?
        .inspect_with_policy(policy)
        .with_role(role)
        .inspect()?
        .plan()?
        .allocate(memory)?
        .map()?
        .decode_with_policy(policy)?;
    absorb_into_session(decoded, rollback)
}

fn session_error(kind: LoadErrorKind, context: ErrorContext) -> LoadError {
    LoadError::new(kind, context)
}

fn session_overflow() -> LoadError {
    session_error(LoadErrorKind::IntegerOverflow, ErrorContext::None)
}

fn validate_session_symbol_names(
    runtime: &RuntimeImageState,
    limits: &SessionLimits,
) -> LoadResult<()> {
    for entry in runtime.metadata().symbols().entries() {
        let len = u32::try_from(runtime.metadata().symbols().name(entry).len())
            .map_err(|_| session_error(LoadErrorKind::ResourceLimit, ErrorContext::None))?;
        limits.check_symbol_name_len(len)?;
    }
    Ok(())
}

fn session_image_metadata_bytes(
    runtime: &RuntimeImageState,
    identity: &ArtifactIdentity,
    soname: Option<&DependencyName>,
) -> LoadResult<u64> {
    runtime
        .metadata()
        .metadata_bytes()
        .checked_add(identity.metadata_bytes())
        .and_then(|bytes| bytes.checked_add(soname.map_or(0, |name| name.as_bytes().len() as u64)))
        .and_then(|bytes| {
            bytes.checked_add(
                runtime.load_segments().len() as u64
                    * core::mem::size_of::<LoadSegmentInfo>() as u64,
            )
        })
        .and_then(|bytes| {
            bytes.checked_add(
                runtime.regions().len() as u64 * core::mem::size_of::<LoadedRegion>() as u64,
            )
        })
        .ok_or_else(session_overflow)
}

/// The retained runtime metadata bytes an imported Ready image keeps in the
/// session: its frozen export surface, its identity/SONAME copy, and its
/// published regions. Charged against
/// `SessionLimits::total_runtime_metadata_bytes` on import.
fn imported_metadata_bytes(descriptor: &PublishedImageDescriptor) -> LoadResult<u64> {
    descriptor
        .exports()
        .metadata_bytes()
        .checked_add(descriptor.identity().metadata_bytes())
        .and_then(|bytes| {
            bytes.checked_add(
                descriptor
                    .soname()
                    .map_or(0, |name| name.as_bytes().len() as u64),
            )
        })
        .and_then(|bytes| {
            bytes.checked_add(
                descriptor.regions().len() as u64 * core::mem::size_of::<PublishedRegion>() as u64,
            )
        })
        .ok_or_else(session_overflow)
}

fn needed_for(
    images: &[SessionImage<RuntimeImageState>],
    requester: ImageId,
    needed_index: u16,
) -> LoadResult<&DependencyName> {
    // Loaded images are stored in discovery order, not image-id order, so a
    // requester id can outrun its dense position once an import interleaves.
    // Look up by id (only loaded images enqueue `DT_NEEDED`, so a requester is
    // always present here).
    images
        .iter()
        .find(|image| image.image_id == requester)
        .and_then(|image| {
            image
                .state
                .metadata()
                .needed()
                .get(usize::from(needed_index))
        })
        .ok_or_else(|| {
            session_error(LoadErrorKind::BadElf, ErrorContext::None).at_stage(LoadStage::Discover)
        })
}

fn enqueue_dependencies(
    queue: &mut DiscoveryQueue,
    requester: ImageId,
    needed: &[DependencyName],
    limits: &SessionLimits,
    stage: LoadStage,
) -> LoadResult<()> {
    for (index, name) in needed.iter().enumerate() {
        limits
            .check_dependency_name_len(name.as_bytes().len() as u32)
            .map_err(|error| error.at_stage(stage))?;
        let index = u16::try_from(index).map_err(|_| {
            session_error(LoadErrorKind::ResourceLimit, ErrorContext::None).at_stage(stage)
        })?;
        queue
            .push(DiscoveryItem::new(requester, index))
            .map_err(|error| error.at_stage(stage))?;
    }
    Ok(())
}

/// Snapshot every relocation's scope decision: the
/// requester, the referenced symbol name and the winning provider — into the
/// published bindings. Symbol-less (`R_ARM_RELATIVE`) relocations record an
/// empty name and no provider; an undefined weak records its name with no
/// provider (it bound to zero). The name copies are charged against the
/// runtime metadata budget.
fn record_bindings(
    operations: &[relocate::SessionRelocation],
    symbols: &[&SymbolTable],
    limits: &SessionLimits,
    usage: &mut SessionUsage,
) -> LoadResult<Vec<RelocationBinding>> {
    /// The byte name of `index` in `owner`'s symbol table, empty when absent.
    fn symbol_name<'t>(symbols: &[&'t SymbolTable], owner: ImageId, index: u32) -> &'t [u8] {
        let Some(table) = symbols.get(owner.get() as usize) else {
            return &[];
        };
        let Some(entry) = table.entry(index) else {
            return &[];
        };
        table.name(entry)
    }

    let mut bindings = Vec::new();
    bindings
        .try_reserve_exact(operations.len())
        .map_err(|_| link_relocation_oom())?;
    for operation in operations {
        let record = operation.record();
        let (name, provider) = match operation.source() {
            RelocationSource::Relative => (alloc::vec![], None),
            RelocationSource::UndefinedWeak => (
                symbol_name(symbols, operation.owner(), record.symbol_index()).to_vec(),
                None,
            ),
            RelocationSource::Symbol(resolved) => (
                symbol_name(symbols, operation.owner(), record.symbol_index()).to_vec(),
                Some(resolved.owner()),
            ),
        };
        // Fixed overhead per binding plus the copied name bytes.
        let bytes = 24u64
            .checked_add(name.len() as u64)
            .ok_or_else(session_overflow)?;
        usage.record_relocation_bindings(bytes, limits)?;
        bindings.push(RelocationBinding::new(
            operation.owner(),
            name,
            provider,
            operation.kind(),
            record.offset(),
        ));
    }
    Ok(bindings)
}

fn publish_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None).at_stage(LoadStage::Publish)
}

fn link_seal_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None).at_stage(LoadStage::LinkSeal)
}

fn link_relocation_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None).at_stage(LoadStage::LinkRelocate)
}

fn scope_session_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None).at_stage(LoadStage::Scope)
}
