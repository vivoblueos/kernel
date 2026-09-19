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

//! The thread-group backend and per-application thread group.
//!
//! A [`ThreadGroup`] is the per-application container the manager creates
//! before any application thread runs. The loader installs the long-lived
//! allocation receipt and startup storage into it, then the runtime attaches
//! member threads and drives the two-phase exit.
//!
//! Membership stays entirely inside this backend. Member threads receive an
//! ordinary retirement cleanup, so neither [`crate::thread::Thread`] nor the
//! scheduler depends on application types.

use crate::sync::SpinLock;
use alloc::{
    sync::{Arc, Weak},
    vec::Vec,
};
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    application::{
        manager::ApplicationHandle,
        publication::KernelLinkReceipt,
        registry::{SystemDsoLease, SystemDsoRegistry, SystemInitBatch},
        start_storage::ApplicationStartStorage,
    },
    thread::{Thread, ThreadNode},
};

/// The lifecycle of a thread group's internal state.
///
/// This is the execution backend's internal state, distinct from the public
/// [`crate::application::manager::ApplicationState`]: the backend tracks the
/// link install and the two-phase exit, while the public state tracks the
/// application's `Loading → Running → Stopping → Terminated/Failed` lifecycle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GroupState {
    /// Created, no threads running, no linked resources installed.
    New,
    /// Linked resources are installed and threads may join.
    Linked,
    /// `ApplicationBeginExit` has run: no new threads may join, and the exit
    /// coordinator is waiting for members to leave before reaping.
    Draining,
    /// The reaper took the group's resources; no further lifecycle calls are
    /// valid.
    Reaped,
}

/// Whether the application's destructors ran before reaping.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExitFini {
    /// Not yet run and not yet skipped.
    Pending,
    /// Normal path: the exit coordinator ran the fini plan and completed.
    Complete,
    /// Abnormal path: the coordinator recorded `SkipFini` and destructors will
    /// not run.
    Skipped,
}

/// Errors the group reports without panicking.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ThreadGroupError {
    AlreadyMember,
    NotMember,
    AlreadyLinked,
    /// `add_member` while the group is draining or reaped.
    Draining,
    /// `begin_exit` on a group that has not installed linked resources.
    NotLinked,
    /// A duplicate `begin_exit` on a group already draining.
    AlreadyDraining,
    /// A lifecycle call that requires a draining group was made too early.
    NotDraining,
    /// `take_resources_for_reap` before fini completed or was skipped.
    FiniPending,
    /// `take_resources_for_reap` while member threads remain.
    MembersRemaining,
    /// The group's resources were already taken.
    AlreadyReaped,
}

struct GroupInner {
    /// The system DSO registry handle used to fail a pending batch on early
    /// exit.
    registry: SystemDsoRegistry,
    state: GroupState,
    /// Strong member references keep every application thread alive until its
    /// scheduler cleanup reports retirement.
    members: Vec<ThreadNode>,
    /// Changed after every removal so the exit coordinator can park without
    /// polling while other members retire.
    members_epoch: Arc<AtomicUsize>,
    /// The application handle the manager minted for this group. Set
    /// once at slot reservation, before the prepare closure runs, so the
    /// exit/init syscalls can reach the manager's slot state after resolving
    /// the current thread through the manager.
    handle: Option<ApplicationHandle>,
    /// The publication receipt keeps every private/system allocation lease
    /// alive until the reaper takes it. Link diagnostics and construction
    /// metadata are discarded once startup storage has been built.
    receipt: Option<KernelLinkReceipt>,
    /// The pinned start-information storage. Owned here for the
    /// application's lifetime so every nested pointer in
    /// [`blueos_header::application::BlueOsApplicationStartInfo`] stays valid
    /// until the last thread exits.
    start_storage: Option<ApplicationStartStorage>,
    /// The pending system initialization batch: installed with
    /// the linked resources, taken by the `ApplicationInitComplete` path to
    /// advance the system candidates to Ready, or failed on early exit.
    pending_system_batch: Option<SystemInitBatch>,
    /// The fini-plan disposition, set only once draining begins.
    fini: ExitFini,
}

/// A per-application thread group. `Clone` yields another handle onto the same
/// resources and membership state.
#[derive(Clone)]
pub struct ThreadGroup {
    inner: Arc<SpinLock<GroupInner>>,
}

/// Weak handle captured by a member's existing retirement cleanup.
///
/// It deliberately lives in the application backend, not in [`Thread`]. A
/// future process backend can install its own cleanup without changing the
/// thread or scheduler types.
#[derive(Clone)]
pub(crate) struct ThreadGroupMembership {
    inner: Weak<SpinLock<GroupInner>>,
}

impl ThreadGroupMembership {
    pub(crate) fn upgrade(&self) -> Option<ThreadGroup> {
        self.inner.upgrade().map(|inner| ThreadGroup { inner })
    }
}

impl ThreadGroup {
    /// Mint a fresh group with no running threads.
    pub fn new(registry: &SystemDsoRegistry) -> Self {
        Self::with_state(GroupState::New, registry.clone())
    }

    fn with_state(state: GroupState, registry: SystemDsoRegistry) -> Self {
        Self {
            inner: Arc::new(SpinLock::new(GroupInner {
                registry: registry.clone(),
                state,
                members: Vec::new(),
                members_epoch: Arc::new(AtomicUsize::new(0)),
                handle: None,
                receipt: None,
                start_storage: None,
                pending_system_batch: None,
                fini: ExitFini::Pending,
            })),
        }
    }

    /// The group's current state.
    pub fn state(&self) -> GroupState {
        self.inner.irqsave_lock().state
    }

    /// Record the application handle the manager minted for this group. Set
    /// once, before the prepare closure runs; a duplicate call is rejected so
    /// a forged second handle cannot rebind the group.
    pub fn set_handle(&self, handle: ApplicationHandle) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if inner.handle.is_some() {
            return Err(ThreadGroupError::AlreadyLinked);
        }
        inner.handle = Some(handle);
        Ok(())
    }

    /// The application handle the manager minted for this group; `None` before
    /// the manager reserved the slot.
    pub fn handle(&self) -> Option<ApplicationHandle> {
        self.inner.irqsave_lock().handle
    }

    /// Install a publication receipt and its pinned start storage, moving
    /// the group from `New` to `Linked`.
    ///
    /// This is the infallible second half of the two-phase install: the
    /// `KernelLinkPublisher::prepare_batch` check already proved the group was
    /// unlinked, and this move only swaps the fully-built product into place.
    /// A reader therefore observes either the old `New` state or a complete
    /// product, never a half-written link map.
    pub fn install_resources(
        &self,
        receipt: KernelLinkReceipt,
        start_storage: ApplicationStartStorage,
    ) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if inner.state != GroupState::New {
            return Err(ThreadGroupError::AlreadyLinked);
        }
        inner.state = GroupState::Linked;
        inner.start_storage = Some(start_storage);
        inner.receipt = Some(receipt);
        Ok(())
    }

    /// Record `thread` in this application's execution set.
    pub fn add_member(&self, thread: ThreadNode) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if matches!(inner.state, GroupState::Draining | GroupState::Reaped) {
            return Err(ThreadGroupError::Draining);
        }
        let id = Thread::id(&thread);
        if inner.members.iter().any(|member| Thread::id(member) == id) {
            return Err(ThreadGroupError::AlreadyMember);
        }
        inner.members.push(thread);
        Ok(())
    }

    /// Remove the member identified by thread id for the reaper's exit
    /// path.
    pub fn remove_member(&self, id: usize) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        let index = inner
            .members
            .iter()
            .position(|member| Thread::id(member) == id)
            .ok_or(ThreadGroupError::NotMember)?;
        inner.members.swap_remove(index);
        bump_members_epoch(&inner.members_epoch);
        Ok(())
    }

    /// Park the calling (exit-coordinator) thread until at most one member
    /// remains — itself. Only valid while the group is draining; the
    /// wait never holds the group lock and wakes on the membership epoch that
    /// every member exit bumps.
    pub fn wait_for_member_exit(&self) -> Result<(), ThreadGroupError> {
        loop {
            let (count, epoch, epoch_value) = {
                let inner = self.inner.irqsave_lock();
                if inner.state != GroupState::Draining {
                    return Err(ThreadGroupError::NotDraining);
                }
                (
                    inner.members.len(),
                    Arc::clone(&inner.members_epoch),
                    inner.members_epoch.load(Ordering::Acquire),
                )
            };
            if count <= 1 {
                return Ok(());
            }
            let _ = crate::sync::atomic_wait(&epoch, epoch_value, crate::time::Tick::MAX);
        }
    }

    /// The number of live member threads.
    pub fn member_count(&self) -> usize {
        self.inner.irqsave_lock().members.len()
    }

    /// Whether the group has no live members, as required before reaping.
    pub fn is_empty(&self) -> bool {
        self.member_count() == 0
    }

    /// A weak group handle captured by the thread's existing cleanup action.
    pub(crate) fn membership(&self) -> ThreadGroupMembership {
        ThreadGroupMembership {
            inner: Arc::downgrade(&self.inner),
        }
    }

    /// Whether `id` is a live member. The manager uses this only for
    /// application lifecycle and child-creation syscalls; it keeps the reverse
    /// mapping out of [`crate::thread::Thread`].
    pub(crate) fn contains_member(&self, id: usize) -> bool {
        self.inner
            .irqsave_lock()
            .members
            .iter()
            .any(|member| Thread::id(member) == id)
    }

    /// Whether the fini disposition is resolved (ran to completion, or
    /// explicitly skipped on the abnormal path) — the reaper's precondition
    /// next to an empty membership.
    pub fn fini_resolved(&self) -> bool {
        let inner = self.inner.irqsave_lock();
        inner.fini != ExitFini::Pending
    }

    /// Install the pending system initialization batch with the linked resources.
    /// The group holds it until the application reports
    /// `ApplicationInitComplete`; an early exit fails it instead.
    pub fn install_pending_system_batch(
        &self,
        batch: SystemInitBatch,
    ) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        // The batch installs during the prepare closure, right after the link
        // publishes — the group is still `New` (the product install follows).
        if inner.state != GroupState::New && inner.state != GroupState::Linked {
            return Err(ThreadGroupError::NotLinked);
        }
        if inner.pending_system_batch.is_some() {
            return Err(ThreadGroupError::AlreadyLinked);
        }
        inner.pending_system_batch = Some(batch);
        Ok(())
    }

    /// Take the pending system initialization batch, for the
    /// `ApplicationInitComplete` path to advance to Ready.
    pub fn take_pending_system_batch(&self) -> Option<SystemInitBatch> {
        let mut inner = self.inner.irqsave_lock();
        inner.pending_system_batch.take()
    }

    /// Attach the first group's system leases to its receipt:
    /// the first-loading group holds ordinary counted leases, released at
    /// group exit like any importer's.
    pub fn attach_system_leases(
        &self,
        leases: Vec<SystemDsoLease>,
    ) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        let Some(receipt) = inner.receipt.as_mut() else {
            return Err(ThreadGroupError::NotLinked);
        };
        receipt.attach_system_leases(leases);
        Ok(())
    }

    /// Begin the two-phase exit: atomically forbid new threads and move the
    /// group from `Linked` to `Draining`. Only the exit coordinator for
    /// this group may call it; a duplicate or out-of-order call is rejected.
    /// An early exit — the application never reported init completion — fails
    /// the pending system batch so no half-initialized descriptor is
    /// published.
    pub fn begin_exit(&self) -> Result<(), ThreadGroupError> {
        let (batch, registry) = {
            let mut inner = self.inner.irqsave_lock();
            match inner.state {
                GroupState::Linked => {
                    // `add_member` checks this state under the same lock, so
                    // no child can join after `Draining` becomes observable.
                    inner.state = GroupState::Draining;
                    (inner.pending_system_batch.take(), inner.registry.clone())
                }
                GroupState::Draining => return Err(ThreadGroupError::AlreadyDraining),
                GroupState::New => return Err(ThreadGroupError::NotLinked),
                GroupState::Reaped => return Err(ThreadGroupError::AlreadyReaped),
            }
        };
        if let Some(batch) = batch {
            let allocations = registry.fail_initialization_batch(batch);
            let mut inner = self.inner.irqsave_lock();
            let receipt = inner
                .receipt
                .as_mut()
                .expect("a linked group must retain its publication receipt");
            receipt.retain_failed_system_allocations(allocations);
        }
        Ok(())
    }

    /// Record that the normal-path destructor plan completed. Must be
    /// called exactly once, while draining.
    pub fn finish_fini(&self) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if inner.state != GroupState::Draining {
            return Err(ThreadGroupError::NotDraining);
        }
        if inner.fini != ExitFini::Pending {
            return Err(ThreadGroupError::AlreadyReaped);
        }
        inner.fini = ExitFini::Complete;
        Ok(())
    }

    /// Record that the destructors are intentionally skipped with a recorded
    /// reason (abnormal path). Must be called exactly once, while
    /// draining, and only before a normal `finish_fini`.
    pub fn skip_fini(&self) -> Result<(), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if inner.state != GroupState::Draining {
            return Err(ThreadGroupError::NotDraining);
        }
        if inner.fini != ExitFini::Pending {
            return Err(ThreadGroupError::AlreadyReaped);
        }
        inner.fini = ExitFini::Skipped;
        Ok(())
    }

    /// Take the group's publication receipt and start storage for reaping,
    /// exactly once. Succeeds only when new threads are forbidden
    /// (`Draining`), no member threads remain, and the fini disposition is
    /// resolved (complete or skipped). The returned receipt owns every
    /// allocation lease the reaper must release; the group moves to `Reaped`
    /// and no further lifecycle calls are valid.
    pub fn take_resources_for_reap(
        &self,
    ) -> Result<(KernelLinkReceipt, Option<ApplicationStartStorage>), ThreadGroupError> {
        let mut inner = self.inner.irqsave_lock();
        if inner.state != GroupState::Draining {
            return Err(match inner.state {
                GroupState::Reaped => ThreadGroupError::AlreadyReaped,
                GroupState::New => ThreadGroupError::NotLinked,
                GroupState::Linked => ThreadGroupError::NotDraining,
                GroupState::Draining => unreachable!(),
            });
        }
        if !inner.members.is_empty() {
            return Err(ThreadGroupError::MembersRemaining);
        }
        if inner.fini == ExitFini::Pending {
            return Err(ThreadGroupError::FiniPending);
        }
        let receipt = inner
            .receipt
            .take()
            .ok_or(ThreadGroupError::AlreadyReaped)?;
        let start_storage = inner.start_storage.take();
        inner.state = GroupState::Reaped;
        Ok((receipt, start_storage))
    }
}

/// Wake every membership waiter after an allocation-free removal. This can run
/// from the scheduler's interrupt-disabled cleanup path because the group uses
/// the kernel's interrupt-saving [`SpinLock`].
fn bump_members_epoch(epoch: &Arc<AtomicUsize>) {
    epoch.fetch_add(1, Ordering::Release);
    let _ = crate::sync::atomic_wake(epoch, usize::MAX);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::thread::{Builder, Entry, Thread};
    use blueos_test_macro::test;

    fn dummy_thread() -> ThreadNode {
        Builder::new(Entry::C(unreachable_entry)).build()
    }

    extern "C" fn unreachable_entry() {
        unreachable!("never scheduled")
    }

    #[test]
    fn a_fresh_group_has_no_members() {
        let registry = SystemDsoRegistry::new();
        let group = ThreadGroup::new(&registry);
        assert_eq!(group.state(), GroupState::New);
        assert!(group.is_empty());
    }

    #[test]
    fn membership_is_counted_and_deduplicated() {
        let registry = SystemDsoRegistry::new();
        let group = ThreadGroup::new(&registry);

        let thread = dummy_thread();
        let id = Thread::id(&thread);
        group.add_member(thread.clone()).unwrap();
        assert_eq!(group.member_count(), 1);
        assert!(!group.is_empty());

        // Duplicate id is rejected, not double-counted.
        assert!(matches!(
            group.add_member(thread),
            Err(ThreadGroupError::AlreadyMember)
        ));
        assert_eq!(group.member_count(), 1);

        group.remove_member(id).unwrap();
        assert!(group.is_empty());
    }
}
