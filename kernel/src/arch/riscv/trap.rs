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

use super::{claim_switch_context, Context};
use crate::{
    arch::{RawContextSwitchHook, RawExceptionFrame},
    scheduler,
    scheduler::ContextSwitchHookHolder,
    thread,
    thread::Thread,
    types::Arc,
};

extern "C" fn handle_switch(hook: RawContextSwitchHook, old_sp: usize) -> usize {
    let hook = unsafe { &mut *hook.cast::<ContextSwitchHookHolder>() };
    scheduler::save_context_finish_hook(hook, old_sp)
}

pub(crate) extern "C" fn handle_ecall_switch_from_raw(
    frame: RawExceptionFrame,
    ra: usize,
) -> usize {
    let from = unsafe { &*frame.cast::<Context>() };
    let hook_ptr = from.a0 as *mut ContextSwitchHookHolder;
    debug_assert!(!hook_ptr.is_null());
    let hook = unsafe { &mut *hook_ptr };
    let next_saved_sp = scheduler::spin_until_ready_to_run(unsafe { hook.next_thread() });
    let old_sp = from as *const _ as usize;
    super::switch_stack_with_hook(hook_ptr.cast(), old_sp, next_saved_sp, ra, handle_switch)
}

// The RISC-V trap entry now lives in bluekernel_arch, but choosing whether an
// interrupt should preempt the current thread is still kernel scheduler policy.
// Keep that decision here until Phase 4 moves context ownership and scheduler
// switch support across the arch boundary.
pub(crate) extern "C" fn might_switch_context_from_raw(
    frame: RawExceptionFrame,
    ra: usize,
) -> usize {
    let from = unsafe { &*frame.cast::<Context>() };
    let old_sp = from as *const _ as usize;
    if !claim_switch_context() {
        return old_sp;
    }
    let old = scheduler::current_thread_ref();
    if old.preempt_count() != 0 {
        return old_sp;
    }
    let Some(next) = scheduler::next_preferred_thread(old.priority()) else {
        return old_sp;
    };
    debug_assert_eq!(next.state(), thread::READY);
    debug_assert_ne!(Thread::id(old), Thread::id(&next));
    let mut hook = ContextSwitchHookHolder::new(next);
    if Thread::id(old) == Thread::id(scheduler::current_idle_thread_ref()) {
        let res = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert_eq!(res, Ok(()));
    } else {
        let res = scheduler::queue_ready_thread(thread::RUNNING, unsafe { Arc::clone_from(old) });
        debug_assert_eq!(res, Ok(()));
    };
    let next_saved_sp = scheduler::spin_until_ready_to_run(unsafe { hook.next_thread() });
    super::switch_stack_with_hook(
        (&mut hook as *mut ContextSwitchHookHolder).cast(),
        old_sp,
        next_saved_sp,
        ra,
        handle_switch,
    )
}
