// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

#![no_std]

use core::fmt::Debug;

/// Interface that the architecture layer must implement.
/// This is the set of arch functions that the scheduler calls.
pub trait ArchInterface {
    /// The architecture-specific context structure type.
    type Context: Default + Debug;

    /// Get the current CPU/hart ID.
    fn current_cpu_id() -> usize;

    /// Get the current stack pointer.
    fn current_sp() -> usize;

    /// Check if local interrupts are enabled.
    fn local_irq_enabled() -> bool;

    /// Enable local interrupts.
    fn enable_local_irq();

    /// Disable local interrupts.
    fn disable_local_irq();

    /// Enter idle state (e.g., WFI instruction).
    fn idle();

    /// Perform context switch to the thread pointed by the hook holder.
    /// This is typically implemented via SVC/ecall.
    fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder);

    /// Pend a context switch to happen at the next opportunity.
    fn pend_switch_context();

    /// Start scheduling — jump to the first thread.
    fn start_schedule(cont: extern "C" fn() -> !);

    /// Send an inter-processor interrupt to the given hart.
    fn send_ipi(hart: usize);

    /// Switch to a different stack and continue execution there.
    /// This is a naked function — never returns.
    fn switch_stack(to_sp: usize, cont: extern "C" fn(sp: usize, old_sp: usize)) -> !;
}

/// Interface that the scheduler layer must implement.
/// This is the set of scheduler functions that the arch layer calls.
pub trait SchedulerInterface {
    /// The scheduler's thread handle type.
    type ThreadHandle: Clone + Send;

    /// Called after arch saves the current context.
    /// Switches the current thread, returns the next thread's stack pointer.
    fn save_context_finish_hook(
        hook: &mut ContextSwitchHookHolder,
        old_sp: usize,
    ) -> usize;

    /// Busy-wait until the given thread has a saved stack pointer.
    /// Returns the saved stack pointer.
    fn spin_until_ready_to_run(t: &Self::ThreadHandle) -> usize;

    /// Get a reference to the current thread.
    fn current_thread_ref() -> Self::ThreadHandle;

    /// Voluntarily relinquish the CPU.
    fn relinquish_me();

    /// Trigger a yield now or flag it for later (if in ISR).
    fn yield_me_now_or_later();

    /// Get the next preferred thread with the given priority or higher.
    fn next_preferred_thread(priority: u8) -> Option<Self::ThreadHandle>;

    /// Get a reference to the current core's idle thread.
    fn current_idle_thread_ref() -> Self::ThreadHandle;

    /// Queue a thread into the ready list.
    fn queue_ready_thread(state: u8, thread: Self::ThreadHandle);

    /// Relinquish the CPU and return the next thread's saved SP.
    fn relinquish_me_and_return_next_sp() -> usize;
}

/// Holds the next-thread pointer during a context switch.
/// Moved here from kernel/scheduler to break the arch↔scheduler cyclic dependency.
///
/// The inner pointer is type-erased (`*const ()`) so that this struct can live
/// in a zero-dependency crate without knowing the concrete Thread type.
/// The scheduler casts it back to `*const Thread` when reading.
pub struct ContextSwitchHookHolder {
    next_thread: *const (),
}

impl ContextSwitchHookHolder {
    /// Create a new holder wrapping the given thread pointer.
    pub fn new<T>(next_thread: *const T) -> Self {
        Self {
            next_thread: next_thread as *const (),
        }
    }

    /// Get the stored thread pointer, cast to the requested type.
    /// # Safety
    /// The caller must ensure the pointer is valid and of the correct type.
    pub unsafe fn next_thread<T>(&self) -> &T {
        &*(self.next_thread as *const T)
    }
}

// Safety: ContextSwitchHookHolder is Send + Sync because the raw pointer
// is only accessed under well-defined synchronization by the scheduler.
unsafe impl Send for ContextSwitchHookHolder {}
unsafe impl Sync for ContextSwitchHookHolder {}