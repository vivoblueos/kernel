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

//! System DSO registry: permit, lease and generation state machine.
//!
//! One [`SystemDsoRegistry`] tracks every mapped system DSO instance by its
//! canonical system path. It answers the single question a resolver needs:
//! for a requested system dependency, is there already a Ready instance to
//! *import*, or must some link *load* it as a candidate?
//!
//! The state machine is driven by unique, non-`Clone` tokens:
//!
//! * [`LoadPermit`] — the sole publication authority for one generation, handed
//!   out exactly once while a slot is `Loading`. Dropping it before
//!   [`SystemDsoRegistry::publish_relocated`] cancels the load (back to
//!   `Vacant`).
//! * [`RelocatedPermit`] — the authority handed back by `publish_relocated`
//!   once the link's relocation/seal stage completed. Dropping it before
//!   [`SystemDsoRegistry::publish_relocated_batch`] also cancels, because
//!   nothing has run a constructor yet.
//! * [`SystemDsoLease`] — one counted reference to a Ready instance. Acquiring
//!   it on the Ready fast path only increments a counter; it never re-maps,
//!   re-relocates or re-runs init. Its `Drop` only decrements
//!   the counter. A reaper explicitly resolves a zero-user instance through
//!   [`SystemDsoRegistry::resolve_quiescence`]; an ordinary failed-link drop
//!   safely leaves a reusable zero-user `Ready` instance instead of stranding
//!   it in an in-flight state with no worker.
//! * [`SystemBatchWait`] — a waiter's ticket for an in-flight closure. A
//!   planner-acquired batch never partially mutates the registry, so concurrent
//!   sessions cannot form an ABBA wait cycle.
//!
//! A system candidate's unique
//! [`AllocationLease`](blueos_loader::AllocationLease) moves from the publisher
//! receipt into the registry when the candidate enters `Initializing`. The
//! registry retains it through `Ready` and hands it to the reaper only when the
//! instance is safe to unload. The registry itself is a plain `Arc<Mutex<_>>`
//! handle; every slow VFS, link, init and fini step runs outside its short lock.

use alloc::{sync::Arc, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering};

use blueos_loader::{
    AllocationLease, DependencyName, ErrorContext, FiniPlan, LoadError, LoadErrorKind, LoadResult,
    PublishedImageDescriptor,
};
use spin::Mutex;

use crate::{
    sync::{atomic_wait, atomic_wake},
    time::Tick,
};

/// The outcome of resolving a quiescent slot.
pub enum QuiescenceResolution {
    /// The zero-lease instance stays `Ready` for a later import.
    KeptCached,
    /// A whole system SCC entered `Unloading`. The worker must run every fini
    /// plan and release every backing before completing the batch.
    Unloaded(SystemUnloadBatch),
}

/// One member handed to the quiescence worker for destruction.
pub struct SystemUnloadBacking {
    pub key: DependencyName,
    pub allocation: AllocationLease,
    pub fini_plan: FiniPlan,
    /// Outgoing SCC dependency leases. They remain live through this member's
    /// fini and drop only after its backing has been released.
    pub dependencies: Vec<SystemDsoLease>,
}

/// Completion token for an atomically quiesced system SCC.
///
/// Its slots remain `Unloading`, so no new link can observe a partially
/// destroyed group. The worker takes the backings, performs fini/release in
/// ordinary thread context, then calls [`SystemDsoRegistry::finish_unload`].
pub struct SystemUnloadBatch {
    inner: Arc<Mutex<RegistryInner>>,
    members: Vec<BatchMember>,
    backings: Vec<SystemUnloadBacking>,
}

impl SystemUnloadBatch {
    pub fn take_backings(&mut self) -> Vec<SystemUnloadBacking> {
        core::mem::take(&mut self.backings)
    }
}

/// The outcome of a batch acquire over a whole declared system closure
pub enum AcquireBatchOutcome {
    /// The entire closure was acquired atomically: `Vacant` slots became
    /// `Loading` (with their permits) and `Ready` slots minted leases.
    Acquired(PreparedSystemBatch),
    /// Some slot is mid-construction; nothing changed and the caller must
    /// wait on the ticket and retry the whole batch.
    Pending(SystemBatchWait),
}

/// The atomically acquired system closure a resolver consumes edge-by-edge.
pub struct PreparedSystemBatch {
    /// First-load candidates: the canonical path key and publication permit.
    pub loads: Vec<(DependencyName, LoadPermit)>,
    /// Ready imports: the canonical path key, lease and shared descriptor.
    pub imports: Vec<(
        DependencyName,
        SystemDsoLease,
        Arc<PublishedImageDescriptor>,
    )>,
}

/// The registry-owned backing of one new system candidate.
///
/// The first-loading application moves these into the registry at batch
/// publication: the instance — not the application receipt — owns the unique
/// allocation, the descriptor and the fini plan from then on.
pub struct SystemCandidateBacking {
    pub descriptor: Arc<PublishedImageDescriptor>,
    pub fini_plan: FiniPlan,
    pub allocation: AllocationLease,
    /// Outgoing dependencies to other system SCCs. They become counted leases
    /// atomically when the whole initialization batch becomes Ready.
    pub dependency_keys: Vec<DependencyName>,
    /// Empty storage pre-reserved for `dependency_keys`, so the Ready
    /// transition and lease minting do not allocate under the registry lock.
    pub dependencies: Vec<SystemDsoLease>,
    /// Every canonical path key in this candidate's system SCC. Internal edges are
    /// structural and do not mint self-sustaining leases.
    pub scc_members: Vec<DependencyName>,
    /// Cached/unloadable policy captured from the immutable system catalog.
    pub keep_cached: bool,
}

/// Publication authority for a batch of `Initializing` slots, minted by
/// [`SystemDsoRegistry::publish_relocated_batch`].
///
/// It must be advanced with [`SystemDsoRegistry::finish_initialization_batch`]
/// once the application reports `ApplicationInitComplete`, or failed through
/// [`SystemDsoRegistry::fail_initialization_batch`] when the application dies
/// first. Dropping it armed fails the batch: no descriptor is ever published
/// and the backings move to `Failed` for the quiescence worker.
pub struct SystemInitBatch {
    inner: Arc<Mutex<RegistryInner>>,
    members: Vec<BatchMember>,
    /// Empty, pre-reserved sink used to return failed candidate allocations to
    /// the owning thread group without allocating during failure handling.
    failure_backings: Vec<AllocationLease>,
    armed: bool,
}

impl SystemInitBatch {
    fn consume(
        mut self,
    ) -> (
        Arc<Mutex<RegistryInner>>,
        Vec<BatchMember>,
        Vec<AllocationLease>,
    ) {
        self.armed = false;
        (
            Arc::clone(&self.inner),
            core::mem::take(&mut self.members),
            core::mem::take(&mut self.failure_backings),
        )
    }
}

impl Drop for SystemInitBatch {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        // An armed token can only be abandoned before ownership is attached to
        // a running group. Hide its half-initialized descriptors and let the
        // registry worker release their backings.
        let registry = SystemDsoRegistry {
            inner: Arc::clone(&self.inner),
        };
        let members = core::mem::take(&mut self.members);
        registry.abandon_initialization_batch(members);
    }
}

/// A batch waiter's ticket for an in-flight system closure.
///
/// The handle keys off the registry-wide resolution epoch, so a wake that
/// resolves only *part* of the closure still causes a safe whole-batch
/// re-check.
pub struct SystemBatchWait {
    observed: usize,
    signal: Arc<AtomicUsize>,
}

impl SystemBatchWait {
    /// Block until some slot of the closure resolved, then return so the
    /// caller re-runs the whole batch acquisition.
    pub fn wait(&self) {
        loop {
            let current = self.signal.load(Ordering::Acquire);
            if current != self.observed {
                break;
            }
            let _ = atomic_wait(&self.signal, current, Tick::MAX);
        }
    }
}

/// Per-canonical-path construction state.
///
/// `Unloading` hides every member of an SCC while its worker runs fini and
/// releases backing memory. `Initializing` hides descriptors until
/// constructors complete; `Failed` retains a failed constructor's backing for
/// deferred release.
enum InstanceState {
    Vacant,
    Loading,
    Relocated,
    /// The batch publication was accepted: the backing, descriptor and fini
    /// plan are registry-owned while the application's constructors run. No
    /// waiter may observe a descriptor here — they stay `Pending` until the
    /// application reports init completion.
    Initializing {
        descriptor: Arc<PublishedImageDescriptor>,
        fini_plan: FiniPlan,
        allocation: AllocationLease,
        dependency_keys: Vec<DependencyName>,
        dependencies: Vec<SystemDsoLease>,
        scc_members: Vec<DependencyName>,
        keep_cached: bool,
    },
    Ready {
        leases: usize,
        descriptor: Arc<PublishedImageDescriptor>,
        fini_plan: FiniPlan,
        /// The instance owns its backing: the unique allocation lease
        /// and its system-to-system dependency leases live with the Ready
        /// state, released only by the quiescence worker.
        allocation: AllocationLease,
        dependencies: Vec<SystemDsoLease>,
        scc_members: Vec<DependencyName>,
        keep_cached: bool,
    },
    /// An SCC's backings have moved to a [`SystemUnloadBatch`]. The state is
    /// not re-acquirable until the worker calls `finish_unload`.
    Unloading,
    /// An initialization token was abandoned before it was attached to a
    /// running group. The worker releases the retained backing and reopens the
    /// slot; no half-initialized descriptor is ever published.
    Failed {
        allocation: AllocationLease,
    },
}

/// Stable identity of one slot generation carried by an initialization or
/// unload batch.
#[derive(Clone, Copy)]
struct BatchMember {
    slot: usize,
    generation: u32,
}

struct Slot {
    key: DependencyName,
    generation: u32,
    state: InstanceState,
}

struct RegistryInner {
    slots: Vec<Slot>,
    /// Registry-wide resolution epoch: bumped whenever any slot resolves
    /// (cancel, Ready publication or quiescence decision). Batch waiters key
    /// off it instead of per-slot signals, so a batch covering several slots
    /// re-checks the whole set atomically.
    resolution: Arc<AtomicUsize>,
}

/// Shared registry handle. `Clone` yields another handle onto the same slot
/// table; each link/thread keeps an independent clone.
pub struct SystemDsoRegistry {
    inner: Arc<Mutex<RegistryInner>>,
}

impl Clone for SystemDsoRegistry {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl SystemDsoRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(RegistryInner {
                slots: Vec::new(),
                resolution: Arc::new(AtomicUsize::new(0)),
            })),
        }
    }

    /// Atomically acquire the whole declared system closure.
    ///
    /// Every slot must be re-acquirable — `Vacant` or `Ready` — in which case
    /// all `Vacant` slots mint a [`LoadPermit`] and all `Ready` slots mint a
    /// [`SystemDsoLease`] plus a shared descriptor, under a single lock hold:
    /// two concurrent sessions can never interleave two half-batches and form
    /// an ABBA cycle. Any in-flight slot leaves the entire set untouched and
    /// returns a [`SystemBatchWait`] ticket; the caller waits outside the lock
    /// and retries the whole batch.
    pub fn acquire_batch(&self, keys: &[DependencyName]) -> AcquireBatchOutcome {
        let mut inner = self.inner.lock();
        // Deterministic canonical-path byte order, de-duplicated.
        let mut ordered: Vec<DependencyName> = keys.to_vec();
        ordered.sort();
        ordered.dedup();
        for key in &ordered {
            let index = ensure_slot(&mut inner.slots, key.clone());
            match inner.slots[index].state {
                InstanceState::Vacant | InstanceState::Ready { .. } => {}
                InstanceState::Loading
                | InstanceState::Relocated
                | InstanceState::Initializing { .. }
                | InstanceState::Unloading
                | InstanceState::Failed { .. } => {
                    return AcquireBatchOutcome::Pending(SystemBatchWait {
                        observed: inner.resolution.load(Ordering::Acquire),
                        signal: Arc::clone(&inner.resolution),
                    });
                }
            }
        }
        let mut loads = Vec::new();
        let mut imports = Vec::new();
        for key in ordered {
            let index = ensure_slot(&mut inner.slots, key.clone());
            let slot = &mut inner.slots[index];
            match &mut slot.state {
                InstanceState::Vacant => {
                    slot.generation = slot.generation.wrapping_add(1);
                    slot.state = InstanceState::Loading;
                    loads.push((
                        key,
                        LoadPermit {
                            inner: Arc::clone(&self.inner),
                            slot: index,
                            generation: slot.generation,
                            armed: true,
                        },
                    ));
                }
                InstanceState::Ready {
                    leases, descriptor, ..
                } => {
                    *leases = leases.saturating_add(1);
                    imports.push((
                        key,
                        SystemDsoLease {
                            inner: Arc::clone(&self.inner),
                            slot: index,
                            generation: slot.generation,
                            key: slot.key.clone(),
                        },
                        descriptor.clone(),
                    ));
                }
                _ => unreachable!("batch pre-check passed"),
            }
        }
        AcquireBatchOutcome::Acquired(PreparedSystemBatch { loads, imports })
    }

    /// Advance a `Loading` slot to `Relocated` once the candidate image's
    /// relocation and seal stage completed. All capacity/identity/
    /// generation checks happen in the link publisher's `prepare_batch` before
    /// this call; this only moves the slot and returns the next token.
    pub fn publish_relocated(&self, permit: LoadPermit) -> LoadResult<RelocatedPermit> {
        let (inner, slot, generation) = permit.consume();
        {
            let mut guard = inner.lock();
            let instance = guard.slots.get_mut(slot).ok_or_else(stale_error)?;
            if instance.generation != generation {
                return Err(stale_error());
            }
            match instance.state {
                InstanceState::Loading => instance.state = InstanceState::Relocated,
                _ => return Err(stale_error()),
            }
        }
        Ok(RelocatedPermit {
            inner,
            slot,
            generation,
            armed: true,
        })
    }

    /// Publish a whole batch of relocated system candidates in one lock hold
    /// Each slot moves `Relocated → Initializing` and the
    /// registry becomes the owner of its backing allocation, descriptor and
    /// fini plan. Waiters stay `Pending` — nothing here publishes a
    /// descriptor. The returned [`SystemInitBatch`] must be advanced with
    /// [`SystemDsoRegistry::finish_initialization_batch`] once the
    /// application reports `ApplicationInitComplete`, or failed through
    /// [`SystemDsoRegistry::fail_initialization_batch`] when the application
    /// dies first.
    pub fn publish_relocated_batch(
        &self,
        permits: Vec<RelocatedPermit>,
        backings: Vec<SystemCandidateBacking>,
    ) -> LoadResult<SystemInitBatch> {
        if permits.len() != backings.len() {
            return Err(stale_error());
        }
        let mut members = Vec::new();
        members
            .try_reserve(permits.len())
            .map_err(|_| registry_oom())?;
        let mut failure_backings = Vec::new();
        failure_backings
            .try_reserve(permits.len())
            .map_err(|_| registry_oom())?;
        for permit in &permits {
            if !Arc::ptr_eq(&self.inner, &permit.inner)
                || members
                    .iter()
                    .any(|member: &BatchMember| member.slot == permit.slot)
            {
                return Err(stale_error());
            }
            members.push(BatchMember {
                slot: permit.slot,
                generation: permit.generation,
            });
        }

        let mut guard = self.inner.lock();
        for member in &members {
            let instance = guard.slots.get(member.slot).ok_or_else(stale_error)?;
            if instance.generation != member.generation
                || !matches!(instance.state, InstanceState::Relocated)
            {
                return Err(stale_error());
            }
        }

        // Every fallible check completed above. Mutate the whole batch while
        // holding one registry lock, so no observer can see a partial
        // Relocated-to-Initializing transition.
        for (permit, backing) in permits.into_iter().zip(backings) {
            let (_, slot, _) = permit.consume();
            let instance = &mut guard.slots[slot];
            instance.state = InstanceState::Initializing {
                descriptor: backing.descriptor,
                fini_plan: backing.fini_plan,
                allocation: backing.allocation,
                dependency_keys: backing.dependency_keys,
                dependencies: backing.dependencies,
                scc_members: backing.scc_members,
                keep_cached: backing.keep_cached,
            };
        }
        drop(guard);

        Ok(SystemInitBatch {
            inner: Arc::clone(&self.inner),
            members,
            failure_backings,
            armed: true,
        })
    }

    /// Complete a published initialization batch: every slot moves
    /// `Initializing → Ready` with one counted lease minted for the
    /// first-loading application group. The first group holds an ordinary
    /// lease like any importer. Called by the
    /// `ApplicationInitComplete` syscall path before the manager marks the
    /// application `Running`; all tokens were validated at publish time, so
    /// this path only moves state.
    pub fn finish_initialization_batch(
        &self,
        batch: SystemInitBatch,
    ) -> LoadResult<Vec<SystemDsoLease>> {
        let (inner, members, _failure_backings) = batch.consume();
        let mut guard = inner.lock();
        let resolution = Arc::clone(&guard.resolution);
        let mut leases = Vec::new();
        leases
            .try_reserve(members.len())
            .map_err(|_| registry_oom())?;

        // Validate the complete transition and every outgoing dependency
        // before mutating a slot. A provider may be an already-Ready import or
        // another member of this initialization batch.
        for member in &members {
            let instance = guard.slots.get(member.slot).ok_or_else(stale_error)?;
            if instance.generation != member.generation {
                return Err(stale_error());
            }
            let InstanceState::Initializing {
                dependency_keys,
                dependencies,
                ..
            } = &instance.state
            else {
                return Err(stale_error());
            };
            if dependencies.capacity() < dependency_keys.len() {
                return Err(registry_oom());
            }
            for dependency in dependency_keys {
                let provider = guard
                    .slots
                    .iter()
                    .find(|provider| &provider.key == dependency)
                    .ok_or_else(stale_error)?;
                match &provider.state {
                    InstanceState::Ready { .. } => {}
                    InstanceState::Initializing { .. } => {
                        let provider_index = guard
                            .slots
                            .iter()
                            .position(|candidate| core::ptr::eq(candidate, provider))
                            .ok_or_else(stale_error)?;
                        if !members.iter().any(|member| member.slot == provider_index) {
                            return Err(stale_error());
                        }
                    }
                    _ => return Err(stale_error()),
                }
            }
        }

        let mut pending_dependencies = Vec::new();
        pending_dependencies
            .try_reserve(members.len())
            .map_err(|_| registry_oom())?;
        for member in &members {
            let instance = guard.slots.get_mut(member.slot).ok_or_else(stale_error)?;
            match core::mem::replace(&mut instance.state, InstanceState::Vacant) {
                InstanceState::Initializing {
                    descriptor,
                    fini_plan,
                    allocation,
                    dependency_keys,
                    dependencies,
                    scc_members,
                    keep_cached,
                } => {
                    instance.state = InstanceState::Ready {
                        leases: 1,
                        descriptor,
                        fini_plan,
                        allocation,
                        dependencies,
                        scc_members,
                        keep_cached,
                    };
                    pending_dependencies.push((member.slot, dependency_keys));
                    leases.push(SystemDsoLease {
                        inner: Arc::clone(&inner),
                        slot: member.slot,
                        generation: member.generation,
                        key: instance.key.clone(),
                    });
                }
                _ => return Err(stale_error()),
            }
        }

        // All candidates are now Ready under the same lock hold. Mint one
        // retained lease for each outgoing cross-SCC edge and attach it to the
        // source instance. Internal SCC edges were removed by the loader.
        for (source_slot, dependency_keys) in pending_dependencies {
            for key in dependency_keys {
                let provider_slot = guard
                    .slots
                    .iter()
                    .position(|provider| provider.key == key)
                    .ok_or_else(stale_error)?;
                let generation = {
                    let provider = &mut guard.slots[provider_slot];
                    let InstanceState::Ready { leases, .. } = &mut provider.state else {
                        return Err(stale_error());
                    };
                    *leases = leases.saturating_add(1);
                    provider.generation
                };
                let dependency = SystemDsoLease {
                    inner: Arc::clone(&inner),
                    slot: provider_slot,
                    generation,
                    key,
                };
                let InstanceState::Ready { dependencies, .. } = &mut guard.slots[source_slot].state
                else {
                    return Err(stale_error());
                };
                dependencies.push(dependency);
            }
        }
        if !members.is_empty() {
            wake_waiters(&resolution);
        }
        drop(guard);
        Ok(leases)
    }

    /// Fail a published initialization batch: the application died before its
    /// init completed, so no descriptor may be published. Each slot returns to
    /// `Vacant` for a generation+1 retry. The returned allocation leases must
    /// remain owned by the failed application group until all of its threads
    /// have stopped, then be released by the reaper.
    pub fn fail_initialization_batch(&self, batch: SystemInitBatch) -> Vec<AllocationLease> {
        let (inner, members, mut failure_backings) = batch.consume();
        let mut guard = inner.lock();
        let resolution = Arc::clone(&guard.resolution);
        let mut changed = false;
        for member in members {
            let Some(instance) = guard.slots.get_mut(member.slot) else {
                continue;
            };
            if instance.generation != member.generation
                || !matches!(instance.state, InstanceState::Initializing { .. })
            {
                continue;
            }
            let InstanceState::Initializing {
                allocation,
                dependencies,
                ..
            } = core::mem::replace(&mut instance.state, InstanceState::Vacant)
            else {
                unreachable!("initializing state was checked before transition")
            };
            // Dependency leases are minted only by the successful Ready
            // transition, so dropping the failed state under the registry lock
            // cannot recursively acquire this lock.
            debug_assert!(dependencies.is_empty());
            debug_assert!(failure_backings.len() < failure_backings.capacity());
            failure_backings.push(allocation);
            changed = true;
        }
        if changed {
            wake_waiters(&resolution);
        }
        drop(guard);
        failure_backings
    }

    /// Handle an initialization token dropped before a running group took
    /// responsibility for its backing. The worker later extracts these
    /// `Failed` allocations and releases them outside the registry lock.
    fn abandon_initialization_batch(&self, members: Vec<BatchMember>) {
        let mut guard = self.inner.lock();
        let resolution = Arc::clone(&guard.resolution);
        let mut changed = false;
        for member in members {
            let Some(instance) = guard.slots.get_mut(member.slot) else {
                continue;
            };
            if instance.generation != member.generation
                || !matches!(instance.state, InstanceState::Initializing { .. })
            {
                continue;
            }
            let InstanceState::Initializing {
                allocation,
                dependencies,
                ..
            } = core::mem::replace(&mut instance.state, InstanceState::Vacant)
            else {
                unreachable!("initializing state was checked before transition")
            };
            debug_assert!(dependencies.is_empty());
            instance.state = InstanceState::Failed { allocation };
            changed = true;
        }
        if changed {
            wake_waiters(&resolution);
        }
    }

    /// Resolve the zero-user SCC containing `key` once the reaper has
    /// quiescence evidence.
    ///
    /// Every member must be Ready with zero counted leases. If any member is
    /// cache-pinned, the whole SCC stays Ready. Otherwise all members move to
    /// `Unloading` in one lock hold and their backings are handed to the
    /// worker; no concurrent acquire can observe a half-destroyed SCC.
    pub fn resolve_quiescence(&self, key: &DependencyName) -> Option<QuiescenceResolution> {
        let mut inner = self.inner.lock();
        let index = inner.slots.iter().position(|slot| &slot.key == key)?;
        let InstanceState::Ready {
            leases: 0,
            scc_members,
            keep_cached: stored_keep_cached,
            ..
        } = &inner.slots[index].state
        else {
            return None;
        };

        let mut members = Vec::new();
        members.try_reserve(scc_members.len()).ok()?;
        for member in scc_members {
            let member_index = inner.slots.iter().position(|slot| &slot.key == member)?;
            if !members.contains(&member_index) {
                members.push(member_index);
            }
        }
        if members.is_empty() {
            members.push(index);
        }

        let mut group_keep_cached = *stored_keep_cached;
        for member in &members {
            let InstanceState::Ready {
                leases: 0,
                keep_cached,
                ..
            } = &inner.slots[*member].state
            else {
                return None;
            };
            group_keep_cached |= *keep_cached;
        }
        if group_keep_cached {
            return Some(QuiescenceResolution::KeptCached);
        }

        let mut backings = Vec::new();
        let mut batch_members = Vec::new();
        backings.try_reserve(members.len()).ok()?;
        batch_members.try_reserve(members.len()).ok()?;
        for member in members {
            let slot = &mut inner.slots[member];
            let state = core::mem::replace(&mut slot.state, InstanceState::Unloading);
            let InstanceState::Ready {
                leases: 0,
                descriptor: _,
                fini_plan,
                allocation,
                dependencies,
                scc_members: _,
                keep_cached: _,
            } = state
            else {
                unreachable!("SCC quiescence was validated before transition")
            };
            batch_members.push(BatchMember {
                slot: member,
                generation: slot.generation,
            });
            backings.push(SystemUnloadBacking {
                key: slot.key.clone(),
                allocation,
                fini_plan,
                dependencies,
            });
        }
        drop(inner);
        Some(QuiescenceResolution::Unloaded(SystemUnloadBatch {
            inner: Arc::clone(&self.inner),
            members: batch_members,
            backings,
        }))
    }

    /// Publish completion of a system SCC's fini/release work. Only now do its
    /// slots become `Vacant` and wake waiters for generation+1.
    pub fn finish_unload(&self, mut batch: SystemUnloadBatch) -> LoadResult<()> {
        if !Arc::ptr_eq(&self.inner, &batch.inner) || !batch.backings.is_empty() {
            return Err(stale_error());
        }
        let mut inner = batch.inner.lock();
        let resolution = Arc::clone(&inner.resolution);
        for member in &batch.members {
            let instance = inner.slots.get(member.slot).ok_or_else(stale_error)?;
            if instance.generation != member.generation
                || !matches!(instance.state, InstanceState::Unloading)
            {
                return Err(stale_error());
            }
        }
        let members = core::mem::take(&mut batch.members);
        let changed = !members.is_empty();
        for member in members {
            let instance = &mut inner.slots[member.slot];
            instance.state = InstanceState::Vacant;
        }
        if changed {
            wake_waiters(&resolution);
        }
        Ok(())
    }

    /// Extract backings from initialization tokens abandoned before a running
    /// group took ownership. The worker releases them outside the registry
    /// lock; allocation failure leaves every `Failed` slot intact for retry on
    /// its next scan.
    pub fn drain_failed_backings(&self) -> Vec<AllocationLease> {
        let mut inner = self.inner.lock();
        let failed = inner
            .slots
            .iter()
            .filter(|slot| matches!(slot.state, InstanceState::Failed { .. }))
            .count();
        let mut backings = Vec::new();
        if backings.try_reserve_exact(failed).is_err() {
            return backings;
        }
        let resolution = Arc::clone(&inner.resolution);
        for slot in &mut inner.slots {
            if !matches!(slot.state, InstanceState::Failed { .. }) {
                continue;
            }
            let InstanceState::Failed { allocation } =
                core::mem::replace(&mut slot.state, InstanceState::Vacant)
            else {
                unreachable!("failed state was checked before transition")
            };
            backings.push(allocation);
        }
        if !backings.is_empty() {
            wake_waiters(&resolution);
        }
        backings
    }
}

impl Default for SystemDsoRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// The unique publication authority for a `Loading` slot.
///
/// Exactly one is minted per generation. It must be advanced with
/// [`SystemDsoRegistry::publish_relocated`]; dropping it armed cancels the load.
pub struct LoadPermit {
    inner: Arc<Mutex<RegistryInner>>,
    slot: usize,
    generation: u32,
    armed: bool,
}

impl LoadPermit {
    /// Disarm and hand back the internals, leaving `self` to drop harmlessly.
    fn consume(mut self) -> (Arc<Mutex<RegistryInner>>, usize, u32) {
        self.armed = false;
        (Arc::clone(&self.inner), self.slot, self.generation)
    }
}

impl Drop for LoadPermit {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        {
            let mut guard = self.inner.lock();
            let resolution = Arc::clone(&guard.resolution);
            let Some(slot) = guard.slots.get_mut(self.slot) else {
                return;
            };
            if slot.generation != self.generation || !matches!(slot.state, InstanceState::Loading) {
                return;
            }
            slot.state = InstanceState::Vacant;
            // Cancelling back to `Vacant` makes the slot re-acquirable.
            wake_waiters(&resolution);
        }
    }
}

/// The publication authority for a `Relocated` slot, returned by
/// [`SystemDsoRegistry::publish_relocated`].
///
/// It must be advanced with [`SystemDsoRegistry::publish_relocated_batch`].
/// Dropping it armed cancels back to `Vacant` — still safe, because no
/// constructor has run.
pub struct RelocatedPermit {
    inner: Arc<Mutex<RegistryInner>>,
    slot: usize,
    generation: u32,
    armed: bool,
}

impl RelocatedPermit {
    fn consume(mut self) -> (Arc<Mutex<RegistryInner>>, usize, u32) {
        self.armed = false;
        (Arc::clone(&self.inner), self.slot, self.generation)
    }
}

impl Drop for RelocatedPermit {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        {
            let mut guard = self.inner.lock();
            let resolution = Arc::clone(&guard.resolution);
            let Some(slot) = guard.slots.get_mut(self.slot) else {
                return;
            };
            if slot.generation != self.generation || !matches!(slot.state, InstanceState::Relocated)
            {
                return;
            }
            slot.state = InstanceState::Vacant;
            wake_waiters(&resolution);
        }
    }
}

/// One counted reference to a Ready system DSO.
///
/// `Drop` only decrements the instance's lease count. A zero-user instance
/// remains `Ready` and reusable until an application reaper explicitly asks
/// the registry to resolve quiescence. This matters for pre-publication link
/// failures: they have no installed group receipt/reaper, so the last imported
/// lease must not leave the provider permanently stuck in an in-flight state.
/// Unloading remains a reaper decision made with quiescence evidence
pub struct SystemDsoLease {
    inner: Arc<Mutex<RegistryInner>>,
    slot: usize,
    generation: u32,
    key: DependencyName,
}

impl SystemDsoLease {
    /// The canonical system catalog path key this lease was minted for.
    #[inline]
    pub fn key(&self) -> &DependencyName {
        &self.key
    }
}

impl Drop for SystemDsoLease {
    fn drop(&mut self) {
        let mut guard = self.inner.lock();
        let Some(slot) = guard.slots.get_mut(self.slot) else {
            return;
        };
        if slot.generation != self.generation {
            return;
        }
        let InstanceState::Ready { leases, .. } = &mut slot.state else {
            return;
        };
        *leases = leases.saturating_sub(1);
    }
}

fn registry_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}

/// Bump the registry-wide resolution epoch and wake every batch waiter.
fn wake_waiters(resolution: &AtomicUsize) {
    resolution.fetch_add(1, Ordering::Release);
    let _ = atomic_wake(resolution, usize::MAX);
}

fn ensure_slot(slots: &mut Vec<Slot>, key: DependencyName) -> usize {
    if let Some(index) = slots.iter().position(|slot| slot.key == key) {
        return index;
    }
    slots.push(Slot {
        key,
        generation: 0,
        state: InstanceState::Vacant,
    });
    slots.len() - 1
}

fn stale_error() -> LoadError {
    LoadError::new(LoadErrorKind::Backend, ErrorContext::None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_loader::{ImageAllocation, TargetAddress};
    use blueos_test_macro::test;

    fn key(path: &[u8]) -> DependencyName {
        DependencyName::from_bytes(path).expect("valid system path")
    }

    #[test]
    fn vacant_batch_grants_one_permit_per_key() {
        let registry = SystemDsoRegistry::new();
        let libc = key(b"/system/lib/libc.so.1");
        let other = key(b"/system/lib/libother.so.1");
        let AcquireBatchOutcome::Acquired(batch) =
            registry.acquire_batch(&[other.clone(), libc.clone(), libc.clone()])
        else {
            panic!("expected acquired batch");
        };
        assert_eq!(batch.loads.len(), 2);
        assert!(batch.imports.is_empty());
        assert_eq!(registry.generation(&libc), Some(1));
        assert_eq!(registry.generation(&other), Some(1));
    }

    #[test]
    fn in_flight_slot_pends_the_whole_batch_without_partial_acquire() {
        let registry = SystemDsoRegistry::new();
        let libc = key(b"/system/lib/libc.so.1");
        let other = key(b"/system/lib/libother.so.1");
        let AcquireBatchOutcome::Acquired(mut first) =
            registry.acquire_batch(core::slice::from_ref(&libc))
        else {
            panic!("expected first batch");
        };
        let permit = first.loads.pop().expect("libc permit").1;
        let AcquireBatchOutcome::Pending(wait) =
            registry.acquire_batch(&[libc.clone(), other.clone()])
        else {
            panic!("expected pending batch");
        };
        assert_eq!(registry.generation(&other), None);
        drop(permit);
        wait.wait();
        let AcquireBatchOutcome::Acquired(second) =
            registry.acquire_batch(&[libc.clone(), other.clone()])
        else {
            panic!("expected retry batch");
        };
        assert_eq!(second.loads.len(), 2);
        assert_eq!(registry.generation(&libc), Some(2));
        assert_eq!(registry.generation(&other), Some(1));
    }

    #[test]
    fn dropping_a_relocated_permit_reopens_the_path_key() {
        let registry = SystemDsoRegistry::new();
        let libc = key(b"/system/lib/libc.so.1");
        let AcquireBatchOutcome::Acquired(mut batch) =
            registry.acquire_batch(core::slice::from_ref(&libc))
        else {
            panic!("expected batch");
        };
        let permit = batch.loads.pop().expect("permit").1;
        let relocated = registry.publish_relocated(permit).expect("relocate");
        drop(relocated);
        let AcquireBatchOutcome::Acquired(retry) =
            registry.acquire_batch(core::slice::from_ref(&libc))
        else {
            panic!("expected retry batch");
        };
        assert_eq!(retry.loads.len(), 1);
        assert_eq!(registry.generation(&libc), Some(2));
    }

    #[test]
    fn draining_failed_backings_reopens_the_slot_without_an_acquire() {
        let registry = SystemDsoRegistry::new();
        let library = key(b"/system/lib/libfailed.so.1");
        let allocation = ImageAllocation::new(TargetAddress::new(0x1000), 0x1000, 0x1000);
        // SAFETY: this test creates the only lease for the synthetic allocation
        // and transfers it exactly once through the registry drain path.
        let lease = unsafe { AllocationLease::new(allocation) };
        registry.inner.lock().slots.push(Slot {
            key: library.clone(),
            generation: 1,
            state: InstanceState::Failed { allocation: lease },
        });

        let drained = registry.drain_failed_backings();
        assert_eq!(drained.len(), 1);
        assert_eq!(*drained[0].allocation(), allocation);

        let AcquireBatchOutcome::Acquired(retry) =
            registry.acquire_batch(core::slice::from_ref(&library))
        else {
            panic!("failed slot was not reopened by the drain");
        };
        assert_eq!(retry.loads.len(), 1);
        assert_eq!(registry.generation(&library), Some(2));
    }
}
