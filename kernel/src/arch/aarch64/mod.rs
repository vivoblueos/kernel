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

pub(crate) mod asm;
mod exception;
pub mod irq;
pub(crate) mod mmu;
pub(crate) mod psci;
pub(crate) mod registers;
pub(crate) mod vector;
pub(crate) mod virt;

use crate::scheduler;
use core::{
    sync::atomic::{self, Ordering},
};
use scheduler::ContextSwitchHookHolder;

// Re-export pure arch items from blueos_arch
pub use blueos_arch::aarch64::{
    Context, NR_SWITCH, TEMP_BOOT_STACK, TempBootStack, current_cpu_id, current_sp,
    disable_local_irq, disable_local_irq_save, enable_local_irq, enable_local_irq_restore, idle,
    local_irq_enabled, pend_switch_context, send_ipi, switch_stack, is_in_interrupt,
};

#[macro_export]
macro_rules! enter_el1 {
    () => {
        "
        mrs x0, cpacr_el1
        orr x0, x0, #(0x3 << 20)
        msr cpacr_el1, x0
        isb
        // Enable CNTP to EL1 for systick.
        mrs     x0, cnthctl_el2
        orr     x0, x0, #3
        msr     cnthctl_el2, x0
        msr     cntvoff_el2, xzr
        // Enable AArch64 in EL1.
        // Calculate per-core stack offset
        // We reserve the top 4KB of each core's 16KB chunk for EL2.
        ldr x1, ={stack_end}
        ldr x12, ={kernel_virt_start}
        sub x1, x1, x12
        mrs x9, mpidr_el1
        and x9, x9, #0xff
        lsl x9, x9, #14
        sub x1, x1, x9
        mov sp, x1
        mov x19, x1
        sub x2, x1, #0x1000
        msr sp_el1, x2
        // Enable to switch into EL2.
        bl {virt_init}
        // Set EL1 sp and mask daif in EL2.
        mov x0, #0x3C5
        msr spsr_el2, x0
        // Enable EL1 MMU while still in EL2.
        ldr x4, ={tmp_stack}
        ldr x12, ={kernel_virt_start}
        sub x4, x4, x12
        add x4, x4, #0x1000
        mov sp, x4
        bl {init_el1_enable_mmu}
        bl {init_el1_boot_linearmap}
        mov sp, x19
        // Set EL1 entry and enter.
        ldr x0, ={stack_start}
        ldr x1, ={stack_end}
        ldr x2, ={cont}
        // adr is PC-relative
        adr x3, {entry}
        msr elr_el2, x3
        eret
        "
    };
}

#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:path, $stack_end:path, $cont: path) => {
        core::arch::naked_asm!(
            crate::enter_el1!(),
            entry = sym crate::arch::aarch64::jump_to_high_va,
            virt_init = sym crate::arch::aarch64::virt::virt_init,
            init_el1_enable_mmu = sym crate::arch::aarch64::mmu::init_el1_enable_mmu,
            init_el1_boot_linearmap = sym crate::arch::aarch64::mmu::init_el1_boot_linearmap,
            kernel_virt_start = const crate::arch::aarch64::mmu::KERNEL_VIRT_START,
            tmp_stack = sym crate::arch::aarch64::TEMP_BOOT_STACK,
            stack_start = sym $stack_start,
            stack_end = sym $stack_end,
            cont = sym $cont,
        )
    };
}

#[naked]
pub(crate) extern "C" fn jump_to_high_va() -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
                ldr x16, ={init}
                br x16
            ",
            init = sym crate::arch::aarch64::init,
        )
    }
}

// FIXME: After adapting to other AArch64 platforms, the
// hardcoded board-specific configuration should be removed.
#[cfg(target_board = "qemu_virt64_aarch64")]
macro_rules! clear_ttbr0_el1 {
    () => {
        "
                // clear ttbr0_el1
                msr ttbr0_el1, xzr
                dsb ish
                isb
                tlbi vmalle1
                dsb ish
                isb
        "
    };
}

// FIXME: After adapting to other AArch64 platforms, the
// hardcoded board-specific configuration should be removed.
#[cfg(not(target_board = "qemu_virt64_aarch64"))]
macro_rules! clear_ttbr0_el1 {
    () => {
        ""
    };
}

#[naked]
pub(crate) extern "C" fn init() -> ! {
    unsafe {
        core::arch::naked_asm!(concat!(
            "
                // set sp
                mrs x8, mpidr_el1
                and x8, x8, #0Xff
                lsl x8, x8, #14
                sub sp, x1, x8
                ",
            clear_ttbr0_el1!(),
            "
                // branch to a far address
                br x2
                "
        ))
    }
}

#[no_mangle]
pub(crate) extern "C" fn start_schedule(cont: extern "C" fn() -> !) {
    let current = crate::scheduler::current_thread_ref();
    current.reset_saved_sp();
    let sp = current.saved_sp();
    unsafe {
        core::arch::asm!(
            "mov lr, #0",
            "mov sp, {sp}",
            "br {cont}",
            sp = in(reg) sp,
            cont = in(reg) cont,
            options(noreturn),
        )
    }
}

#[inline(always)]
#[allow(clippy::empty_loop)]
pub(crate) extern "C" fn restore_context_with_hook(hook: *mut ContextSwitchHookHolder) -> ! {
    switch_context_with_hook(hook);
    loop {}
}

#[inline(never)]
pub(crate) extern "C" fn svc_switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    unsafe {
        core::arch::asm!(
            "svc #0",
            in("x0") hook as usize,
            in("x8") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline]
pub(crate) extern "C" fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    svc_switch_context_with_hook(hook)
}

pub fn secondary_cpu_setup(psci_base: u32) {
    atomic::fence(Ordering::SeqCst);
    let secondary_entry = mmu::kernel_virt_to_phys(crate::boot::_start as usize);
    for i in 1..blueos_kconfig::CONFIG_NUM_CORES {
        psci::cpu_on(psci_base, i as usize, secondary_entry, 0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_context_size() {
        assert_eq!(core::mem::size_of::<Context>(), 960 + 8);
    }
}