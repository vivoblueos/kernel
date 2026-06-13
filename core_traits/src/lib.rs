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
    type Context: Default + Debug;

    fn current_cpu_id() -> usize;
    fn current_sp() -> usize;
    fn local_irq_enabled() -> bool;
    fn enable_local_irq();
    fn disable_local_irq();
    fn idle();
    fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder);
    fn pend_switch_context();
    fn start_schedule(cont: extern "C" fn() -> !);
    fn send_ipi(hart: usize);
    fn switch_stack(to_sp: usize, cont: extern "C" fn(sp: usize, old_sp: usize)) -> !;
}

/// Interface that the scheduler layer must implement.
/// This is the set of scheduler functions that the arch layer calls.
pub trait SchedulerInterface {
    type ThreadHandle: Clone + Send;

    fn save_context_finish_hook(hook: &mut ContextSwitchHookHolder, old_sp: usize) -> usize;

    fn spin_until_ready_to_run(t: &Self::ThreadHandle) -> usize;
    fn current_thread_ref() -> Self::ThreadHandle;
    fn relinquish_me();
    fn yield_me_now_or_later();
    fn next_preferred_thread(priority: u8) -> Option<Self::ThreadHandle>;
    fn current_idle_thread_ref() -> Self::ThreadHandle;
    fn queue_ready_thread(state: u8, thread: Self::ThreadHandle);
    fn relinquish_me_and_return_next_sp() -> usize;
}

/// Holds the next-thread pointer during a context switch.
/// Moved here from kernel/scheduler to break the arch↔scheduler cyclic dependency.
pub struct ContextSwitchHookHolder {
    next_thread: *const (),
}

impl ContextSwitchHookHolder {
    pub fn new<T>(next_thread: *const T) -> Self {
        Self {
            next_thread: next_thread as *const (),
        }
    }

    /// # Safety
    /// The caller must ensure the pointer is valid and of the correct type.
    pub unsafe fn next_thread<T>(&self) -> &T {
        &*(self.next_thread as *const T)
    }
}

// Safety: raw pointer only accessed under well-defined synchronization.
unsafe impl Send for ContextSwitchHookHolder {}
unsafe impl Sync for ContextSwitchHookHolder {}
