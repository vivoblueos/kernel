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

//! Single application manager: slot table, generation-ABA handles and the
//! explicit state machine.
//!
//! One [`ApplicationManager`] is the only entry through which an application is
//! launched — external syscalls and boot bootstrap both go through
//! [`ApplicationManager::launch`] with an [`OwnedLaunchRequest`]; there is no
//! "boot fast path" that calls a loader directly. The manager owns a
//! slot table keyed by request identity; each slot carries a monotonic
//! `generation` so a forged or stale [`ApplicationHandle`] is rejected.
//!
//! The slow prepare/link step runs *outside* the short table lock; only slot reservation,
//! queries and state transitions take the lock.
//!
//! [`ApplicationManager::release`] is the recycle primitive the reaper
//! drives after quiescence: it returns a finished slot to `Vacant` so a later
//! launch of the same identity reuses it with a bumped generation.

use alloc::{sync::Arc, vec::Vec};
use spin::Mutex;

use crate::application::{group::ThreadGroup, registry::SystemDsoRegistry};

/// The lifecycle states of a live application.
///
/// The slot-level "no application" state is [`SlotState::Vacant`], which is not
/// an `ApplicationState`: it means the slot is free for reuse, not that an
/// application is in some phase.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ApplicationState {
    Loading,
    Running,
    Stopping,
    Terminated,
    Failed,
}

/// A versioned application handle: slot index plus the generation that slot had
/// when the handle was minted. Generation makes a stale handle fail after the
/// slot is recycled. It is an internal manager capability and never crosses
/// the application ABI boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApplicationHandle {
    pub slot: u32,
    pub generation: u32,
}

/// Errors reported by application lifecycle operations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ApplicationLaunchError {
    PrepareFailed,
    StaleGeneration,
    AlreadyReleased,
    InvalidTransition {
        from: ApplicationState,
        to: ApplicationState,
    },
}

/// An owned launch request. ELF and namespace validation happen in the loader.
pub struct OwnedLaunchRequest {
    identity: Vec<u8>,
}

impl OwnedLaunchRequest {
    pub fn new(identity: Vec<u8>) -> Self {
        Self { identity }
    }
}

/// Per-`(identity)` construction slot.
enum SlotState {
    /// Free for reuse. A vacant slot has no live application.
    Vacant,
    Occupied(ApplicationState),
}

struct Slot {
    identity: Vec<u8>,
    generation: u32,
    state: SlotState,
    group: ThreadGroup,
}

impl Slot {
    /// Explicit `expected → next` transition; an illegal transition returns the
    /// error instead of silently crossing states.
    fn transition(
        &mut self,
        from: ApplicationState,
        to: ApplicationState,
    ) -> Result<(), ApplicationLaunchError> {
        if !matches!(self.state, SlotState::Occupied(state) if state == from) {
            return Err(ApplicationLaunchError::InvalidTransition {
                from: occupied_state(&self.state),
                to,
            });
        }
        self.state = SlotState::Occupied(to);
        Ok(())
    }
}

struct Inner {
    slots: Vec<Slot>,
}

/// Shared manager handle. `Clone` yields another handle onto the same slot
/// table; each thread keeps an independent clone.
pub struct ApplicationManager {
    inner: Arc<Mutex<Inner>>,
    /// The system DSO registry, minted into every thread group so an early
    /// exit can fail its pending initialization batch.
    registry: SystemDsoRegistry,
}

impl ApplicationManager {
    pub fn new(registry: SystemDsoRegistry) -> Self {
        Self {
            inner: Arc::new(Mutex::new(Inner { slots: Vec::new() })),
            registry,
        }
    }

    /// Launch an application.
    ///
    /// The slot is reserved (→ `Loading`) and a fresh not-yet-running
    /// [`ThreadGroup`] is minted under the short table lock; the caller's
    /// `prepare` then runs *outside* the lock so VFS, linking, cache maintenance
    /// and thread creation do not block other queries or launches. The closure
    /// receives the group and installs the linked resources. On success
    /// the slot *stays* `Loading`: the public state only becomes `Running` when
    /// the application's init plan completed and it reported
    /// `ApplicationInitComplete`, accepted through
    /// [`ApplicationManager::complete_init`]. On `prepare` failure the slot is
    /// left as `Failed` for the deferred reaper.
    pub fn launch<F>(
        &self,
        request: OwnedLaunchRequest,
        prepare: F,
    ) -> Result<ApplicationHandle, ApplicationLaunchError>
    where
        F: FnOnce(&ThreadGroup) -> Result<(), ApplicationLaunchError>,
    {
        self.launch_with_group(request, prepare).0
    }

    /// Launch and return the exact group created for the attempt. The service
    /// uses this to register both successful and failed attempts with the
    /// reaper without looking the group up again by a non-unique identity.
    pub(crate) fn launch_with_group<F>(
        &self,
        request: OwnedLaunchRequest,
        prepare: F,
    ) -> (
        Result<ApplicationHandle, ApplicationLaunchError>,
        ThreadGroup,
    )
    where
        F: FnOnce(&ThreadGroup) -> Result<(), ApplicationLaunchError>,
    {
        let group = ThreadGroup::new(&self.registry);
        let prepare_group = group.clone();
        let (slot, generation) = {
            let mut inner = self.inner.lock();
            reserve_slot(&mut inner.slots, request.identity, group)
        };
        let handle = ApplicationHandle {
            slot: slot as u32,
            generation,
        };
        // Bind the minted handle before the prepare closure runs so an
        // application member thread can recover the manager slot after the
        // manager resolves its thread id.
        if prepare_group.set_handle(handle).is_err() {
            // A fresh group always accepts its first handle; failure here means
            // an internal invariant broke, not a caller error.
            let mut inner = self.inner.lock();
            let instance = inner
                .slots
                .get_mut(slot)
                .expect("a reserved slot stays present");
            instance.state = SlotState::Occupied(ApplicationState::Failed);
            return (Err(ApplicationLaunchError::PrepareFailed), prepare_group);
        }

        let result = prepare(&prepare_group);

        let mut inner = self.inner.lock();
        let instance = inner
            .slots
            .get_mut(slot)
            .expect("a reserved slot stays present");
        if instance.generation != generation {
            return (Err(ApplicationLaunchError::StaleGeneration), prepare_group);
        }
        let result = match result {
            Ok(()) => Ok(handle),
            Err(error) => {
                instance.state = SlotState::Occupied(ApplicationState::Failed);
                Err(error)
            }
        };
        (result, prepare_group)
    }

    /// Accept the application's init completion and move its public state from
    /// `Loading` to `Running`. Only the validated
    /// `ApplicationInitComplete` syscall path may call this — the syscall
    /// resolves the group from the current thread id and checks the
    /// handle against the group, so a foreign thread cannot complete another
    /// application's init.
    pub fn complete_init(&self, handle: ApplicationHandle) -> Result<(), ApplicationLaunchError> {
        let mut inner = self.inner.lock();
        let slot = inner
            .slots
            .get_mut(handle.slot as usize)
            .ok_or(ApplicationLaunchError::StaleGeneration)?;
        if slot.generation != handle.generation {
            return Err(ApplicationLaunchError::StaleGeneration);
        }
        slot.transition(ApplicationState::Loading, ApplicationState::Running)
    }

    /// Move a running application's public state to `Stopping` when its exit
    /// coordinator calls `ApplicationBeginExit`. The syscall path derives
    /// the handle from the current thread's group, so a foreign thread
    /// cannot stop another application.
    pub fn begin_exit(&self, handle: ApplicationHandle) -> Result<(), ApplicationLaunchError> {
        let mut inner = self.inner.lock();
        let slot = inner
            .slots
            .get_mut(handle.slot as usize)
            .ok_or(ApplicationLaunchError::StaleGeneration)?;
        if slot.generation != handle.generation {
            return Err(ApplicationLaunchError::StaleGeneration);
        }
        slot.transition(ApplicationState::Running, ApplicationState::Stopping)
    }

    /// Close an application's public lifecycle once its group resources were
    /// released: `Stopping` becomes the `Terminated` terminal state, and a
    /// launch that already failed keeps its `Failed` terminal state.
    /// Called by the deferred reaper; it also reaches this point for the
    /// abnormal paths where the main thread died without reporting exit
    /// (`Loading`/`Running` → `Terminated`, the group's fini was skipped by the
    /// reaper). The slot then becomes releasable.
    pub fn finish(&self, handle: ApplicationHandle) -> Result<(), ApplicationLaunchError> {
        let mut inner = self.inner.lock();
        let slot = inner
            .slots
            .get_mut(handle.slot as usize)
            .ok_or(ApplicationLaunchError::StaleGeneration)?;
        if slot.generation != handle.generation {
            return Err(ApplicationLaunchError::StaleGeneration);
        }
        match slot.state {
            SlotState::Vacant => Err(ApplicationLaunchError::AlreadyReleased),
            SlotState::Occupied(ApplicationState::Failed) => Ok(()),
            SlotState::Occupied(_) => {
                slot.state = SlotState::Occupied(ApplicationState::Terminated);
                Ok(())
            }
        }
    }

    /// Whether a handle names a live manager slot.
    pub fn contains(&self, handle: ApplicationHandle) -> bool {
        let inner = self.inner.lock();
        let Some(slot) = inner.slots.get(handle.slot as usize) else {
            return false;
        };
        if slot.generation != handle.generation {
            return false;
        }
        matches!(slot.state, SlotState::Occupied(_))
    }

    /// Resolve the application backend that owns a live thread.
    ///
    /// Threads and the scheduler deliberately retain no application pointer.
    /// Only the infrequent application lifecycle syscalls need this reverse
    /// lookup; keeping it in the manager preserves that boundary. A future
    /// process backend can provide its own lookup without changing `Thread`.
    pub(crate) fn group_for_thread(&self, id: usize) -> Option<ThreadGroup> {
        let inner = self.inner.lock();
        inner
            .slots
            .iter()
            .find(|slot| {
                matches!(slot.state, SlotState::Occupied(_)) && slot.group.contains_member(id)
            })
            .map(|slot| slot.group.clone())
    }

    /// Find the handle reserved for an identity. This is used internally when
    /// launch preparation failed but the reaper still needs the group.
    #[cfg(test)]
    fn handle_by_identity(&self, identity: &[u8]) -> Option<ApplicationHandle> {
        let inner = self.inner.lock();
        let (index, slot) =
            inner.slots.iter().enumerate().find(|(_, s)| {
                matches!(s.state, SlotState::Occupied(_)) && s.identity == identity
            })?;
        Some(ApplicationHandle {
            slot: index as u32,
            generation: slot.generation,
        })
    }

    #[cfg(test)]
    fn state(&self, handle: ApplicationHandle) -> Option<ApplicationState> {
        let inner = self.inner.lock();
        let slot = inner.slots.get(handle.slot as usize)?;
        if slot.generation != handle.generation {
            return None;
        }
        match slot.state {
            SlotState::Vacant => None,
            SlotState::Occupied(state) => Some(state),
        }
    }

    /// Return a finished application's slot to `Vacant` so a later launch of the
    /// same identity reuses it with a bumped generation, preventing ABA reuse.
    /// Only the
    /// deferred reaper may call this, and only after [`ApplicationManager::finish`]
    /// moved the slot into a terminal state — the two-phase exit
    /// (`Running → Stopping → Terminated`) or a recorded `Failed`.
    pub fn release(&self, handle: ApplicationHandle) -> Result<(), ApplicationLaunchError> {
        let mut inner = self.inner.lock();
        let slot = inner
            .slots
            .get_mut(handle.slot as usize)
            .ok_or(ApplicationLaunchError::StaleGeneration)?;
        if slot.generation != handle.generation {
            return Err(ApplicationLaunchError::StaleGeneration);
        }
        match slot.state {
            SlotState::Vacant => Err(ApplicationLaunchError::AlreadyReleased),
            SlotState::Occupied(ApplicationState::Terminated)
            | SlotState::Occupied(ApplicationState::Failed) => {
                slot.state = SlotState::Vacant;
                Ok(())
            }
            SlotState::Occupied(state) => Err(ApplicationLaunchError::InvalidTransition {
                from: state,
                to: ApplicationState::Terminated,
            }),
        }
    }
}

impl Default for ApplicationManager {
    fn default() -> Self {
        Self::new(SystemDsoRegistry::new())
    }
}

impl Clone for ApplicationManager {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            registry: self.registry.clone(),
        }
    }
}

fn occupied_state(state: &SlotState) -> ApplicationState {
    match state {
        SlotState::Occupied(state) => *state,
        SlotState::Vacant => ApplicationState::Terminated,
    }
}

/// Reserve a slot for `identity` and return `(index, generation)`, setting the
/// slot to `Loading` and installing `group` as its thread group. Prefers a
/// `Vacant` slot already bound to this identity (so re-launch reuses the slot
/// with a bumped generation), then any `Vacant` slot, then appends a fresh one
fn reserve_slot(slots: &mut Vec<Slot>, identity: Vec<u8>, group: ThreadGroup) -> (usize, u32) {
    if let Some(index) = slots
        .iter()
        .position(|s| matches!(s.state, SlotState::Vacant) && s.identity == identity)
    {
        let slot = &mut slots[index];
        slot.group = group;
        slot.generation = slot.generation.wrapping_add(1);
        slot.state = SlotState::Occupied(ApplicationState::Loading);
        return (index, slot.generation);
    }
    if let Some(index) = slots
        .iter()
        .position(|s| matches!(s.state, SlotState::Vacant))
    {
        let slot = &mut slots[index];
        slot.identity = identity;
        slot.group = group;
        slot.generation = slot.generation.wrapping_add(1);
        slot.state = SlotState::Occupied(ApplicationState::Loading);
        return (index, slot.generation);
    }
    slots.push(Slot {
        identity,
        generation: 1,
        state: SlotState::Occupied(ApplicationState::Loading),
        group,
    });
    (slots.len() - 1, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    fn request(identity: &[u8]) -> OwnedLaunchRequest {
        OwnedLaunchRequest::new(identity.to_vec())
    }

    #[test]
    fn relaunch_after_release_bumps_the_generation() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let first = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        // A prepared launch stays Loading until the init plan completed.
        assert_eq!(manager.state(first), Some(ApplicationState::Loading));
        manager.complete_init(first).unwrap();
        assert_eq!(manager.state(first), Some(ApplicationState::Running));
        // The full two-phase exit runs before the slot is recyclable.
        manager.begin_exit(first).unwrap();
        assert_eq!(manager.state(first), Some(ApplicationState::Stopping));
        manager.finish(first).unwrap();
        assert_eq!(manager.state(first), Some(ApplicationState::Terminated));
        manager.release(first).unwrap();

        let second = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        // Same slot reused, generation bumped: distinct ABA handle.
        assert_eq!(first.slot, second.slot);
        assert_ne!(first.generation, second.generation);
        assert!(!manager.contains(first));
    }

    #[test]
    fn init_completion_requires_the_loading_state() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let handle = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        manager.complete_init(handle).unwrap();
        // A second init completion on a Running application is an illegal
        // transition, not an idempotent no-op.
        assert!(matches!(
            manager.complete_init(handle),
            Err(ApplicationLaunchError::InvalidTransition { .. })
        ));
    }

    #[test]
    fn stale_and_forged_handles_are_rejected() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let handle = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        assert!(manager.contains(handle));

        // Forged generation.
        let forged = ApplicationHandle {
            slot: handle.slot,
            generation: handle.generation.wrapping_add(1),
        };
        assert!(!manager.contains(forged));

        // Out-of-range slot.
        assert!(!manager.contains(ApplicationHandle {
            slot: 999,
            generation: 0,
        }));
    }

    #[test]
    fn failed_prepare_leaves_a_failed_slot_for_reaping() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let err = manager
            .launch(request(b"app"), |_| {
                Err(ApplicationLaunchError::PrepareFailed)
            })
            .unwrap_err();
        assert!(matches!(err, ApplicationLaunchError::PrepareFailed));

        let failed = manager.handle_by_identity(b"app").unwrap();
        assert_eq!(manager.state(failed), Some(ApplicationState::Failed));
    }

    #[test]
    fn releasing_an_already_released_slot_is_rejected() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let handle = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        manager.complete_init(handle).unwrap();
        manager.begin_exit(handle).unwrap();
        manager.finish(handle).unwrap();
        manager.release(handle).unwrap();
        assert!(matches!(
            manager.release(handle),
            Err(ApplicationLaunchError::AlreadyReleased)
        ));
    }

    #[test]
    fn release_requires_a_terminal_state() {
        let manager = ApplicationManager::new(SystemDsoRegistry::new());
        let handle = manager.launch(request(b"app"), |_| Ok(())).unwrap();
        // A live application cannot be released out from under its group.
        assert!(matches!(
            manager.release(handle),
            Err(ApplicationLaunchError::InvalidTransition { .. })
        ));
        manager.complete_init(handle).unwrap();
        assert!(matches!(
            manager.release(handle),
            Err(ApplicationLaunchError::InvalidTransition { .. })
        ));
        // A failed launch, however, is already terminal and recyclable.
        let err = manager
            .launch(request(b"broken"), |_| {
                Err(ApplicationLaunchError::PrepareFailed)
            })
            .unwrap_err();
        assert!(matches!(err, ApplicationLaunchError::PrepareFailed));
        let failed = manager.handle_by_identity(b"broken").unwrap();
        assert_eq!(manager.state(failed), Some(ApplicationState::Failed));
        manager.release(failed).unwrap();
        assert!(!manager.contains(failed));
    }
}
