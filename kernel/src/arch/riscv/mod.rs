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

pub mod trap;

// Re-export types, constants, and pure-arch functions from blueos_arch.
pub use blueos_arch::riscv::{
    bootstrap, current_cpu_id, current_sp, disable_local_irq, disable_local_irq_save,
    enable_local_irq, enable_local_irq_restore, idle, local_irq_enabled, switch_stack, Context,
    IsrContext, MIE_MEIE, MIE_MSIE, MIE_MTIE, MIE_SEIE, MIE_SSIE, MIE_STIE, MSTATUS_MIE,
    MSTATUS_MPIE, MSTATUS_MPP_M, MSTATUS_MPP_MASK, MSTATUS_MPP_S, MSTATUS_MPP_U, NR_SWITCH,
};
pub use blueos_arch::riscv::irq as irq;

use crate::{boards, irq as sysirq, scheduler, scheduler::ContextSwitchHookHolder};
use core::{
    cell::Cell,
    sync::atomic::{compiler_fence, Ordering},
};
pub use trap::*;

pub(crate) const NUM_CORES: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;

// FIXME: We don't need atomic here.
static mut PENDING_SWITCH_CONTEXT: [Cell<bool>; NUM_CORES] =
    [const { Cell::new(false) }; NUM_CORES];

#[inline]
pub(crate) extern "C" fn pend_switch_context() {
    if !sysirq::is_in_irq() {
        scheduler::relinquish_me();
        return;
    }
    let level = disable_local_irq_save();
    let id = current_cpu_id();
    unsafe { PENDING_SWITCH_CONTEXT[id].set(true) };
    enable_local_irq_restore(level);
}

#[inline]
pub(crate) extern "C" fn claim_switch_context() -> bool {
    let level = disable_local_irq_save();
    let id = current_cpu_id();
    let ok = unsafe { PENDING_SWITCH_CONTEXT[id].get() };
    unsafe { PENDING_SWITCH_CONTEXT[id].set(false) };
    enable_local_irq_restore(level);
    ok
}

pub(crate) extern "C" fn ecall_switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    unsafe {
        core::arch::asm!(
            "ecall",
            in("a0") hook as usize,
            in("a7") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline(always)]
pub(crate) extern "C" fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    ecall_switch_context_with_hook(hook)
}

#[inline(always)]
#[allow(clippy::empty_loop)]
pub(crate) extern "C" fn restore_context_with_hook(hook: *mut ContextSwitchHookHolder) -> ! {
    switch_context_with_hook(hook);
    unreachable!("Should have switched to another thread");
}

pub(crate) extern "C" fn start_schedule(cont: extern "C" fn() -> !) {
    let current = crate::scheduler::current_thread_ref();
    current.reset_saved_sp();
    let sp = current.saved_sp();
    unsafe {
        core::arch::asm!(
            "li ra, 0",
            "mv sp, {sp}",
            "jalr x0, {cont}, 0",
            sp = in(reg) sp,
            cont = in(reg) cont,
            options(noreturn),
        )
    }
}

pub(crate) extern "C" fn send_ipi(hart: usize) {
    boards::send_ipi(hart);
}