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
pub(crate) mod exception;
pub mod irq;
pub(crate) mod mmu;
pub(crate) mod psci;
pub(crate) mod registers;
pub(crate) mod vector;
pub(crate) mod virt;

use crate::{arch::registers::mpidr_el1::MPIDR_EL1, scheduler};
use core::sync::{
    atomic,
    atomic::{AtomicU8, Ordering},
};
use tock_registers::interfaces::Readable;

pub use bluekernel_arch::aarch64::context::{Context, IsrContext};
pub use bluekernel_arch::aarch64::{
    restore_context_with_hook, switch_context_with_hook, switch_stack, NR_SWITCH,
};

#[no_mangle]
pub extern "C" fn aarch64_virt_init() {
    virt::virt_init();
}

#[no_mangle]
pub extern "C" fn aarch64_enable_mmu() {
    mmu::enable_mmu();
}

macro_rules! disable_interrupt {
    () => {
        "
        msr daifset, #3
        "
    };
}

macro_rules! enable_interrupt {
    () => {
        "
        msr daifclr, #3
        "
    };
}

// Temporary stack used during early boot (before MMU is enabled).
#[repr(C, align(16))]
pub struct TempBootStack([u8; 4096]);
pub static mut TEMP_BOOT_STACK: TempBootStack = TempBootStack([0u8; 4096]);

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
        add x4, x4, #0x1000
        mov sp, x4
        bl {enable_mmu}
        mov sp, x19
        // Set EL1 entry and enter.
        ldr x0, ={stack_start}
        ldr x2, ={cont}
        adr x3, {entry}
        msr elr_el2, x3
        eret
        "
    };
}

#[macro_export]
macro_rules! aarch64_save_context_prologue {
    () => {
        "
        sub sp, sp, #{stack_size}
        str lr, [sp, #{lr}]
        "
    };
}

#[macro_export]
macro_rules! aarch64_restore_context_epilogue {
    () => {
        "
        ldr lr, [sp, #{lr}]
        add sp, sp, #{stack_size}
        "
    };
}

#[macro_export]
macro_rules! aarch64_save_context {
    () => {
        "
        stp x0, x1, [sp, #{x0}]
        stp x2, x3, [sp, #{x2}]
        stp x4, x5, [sp, #{x4}]
        stp x6, x7, [sp, #{x6}]
        stp x8, x9, [sp, #{x8}]
        stp x10, x11, [sp, #{x10}]
        stp x12, x13, [sp, #{x12}]
        stp x14, x15, [sp, #{x14}]
        stp x16, x17, [sp, #{x16}]
        stp x18, x19, [sp, #{x18}]
        stp x20, x21, [sp, #{x20}]
        stp x22, x23, [sp, #{x22}]
        stp x24, x25, [sp, #{x24}]
        stp x26, x27, [sp, #{x26}]
        stp x28, x29, [sp, #{x28}]
        mrs x8, elr_el1
        str x8, [sp, #{elr}]
        mrs x8, spsr_el1
        str x8, [sp, #{spsr}]
        stp q0, q1, [sp, #{v0}]
        stp q2, q3, [sp, #{v2}]
        stp q4, q5, [sp, #{v4}]
        stp q6, q7, [sp, #{v6}]
        stp q8, q9, [sp, #{v8}]
        stp q10, q11, [sp, #{v10}]
        stp q12, q13, [sp, #{v12}]
        stp q14, q15, [sp, #{v14}]
        stp q16, q17, [sp, #{v16}]
        stp q18, q19, [sp, #{v18}]
        stp q20, q21, [sp, #{v20}]
        stp q22, q23, [sp, #{v22}]
        stp q24, q25, [sp, #{v24}]
        stp q26, q27, [sp, #{v26}]
        stp q28, q29, [sp, #{v28}]
        stp q30, q31, [sp, #{v30}]
        mrs x8, fpcr
        str x8, [sp, #{fpcr}]
        mrs x8, fpsr
        str x8, [sp, #{fpsr}]   
        "
    };
}

#[macro_export]
macro_rules! aarch64_restore_context {
    () => {
        "
        ldr x8, [sp, #{fpcr}]
        msr fpcr, x8
        ldr x8, [sp, #{fpsr}]
        msr fpsr, x8
        ldp q0, q1, [sp, #{v0}]
        ldp q2, q3, [sp, #{v2}]
        ldp q4, q5, [sp, #{v4}]
        ldp q6, q7, [sp, #{v6}]
        ldp q8, q9, [sp, #{v8}]
        ldp q10, q11, [sp, #{v10}]
        ldp q12, q13, [sp, #{v12}]
        ldp q14, q15, [sp, #{v14}]
        ldp q16, q17, [sp, #{v16}]
        ldp q18, q19, [sp, #{v18}]
        ldp q20, q21, [sp, #{v20}]
        ldp q22, q23, [sp, #{v22}]
        ldp q24, q25, [sp, #{v24}]
        ldp q26, q27, [sp, #{v26}]
        ldp q28, q29, [sp, #{v28}]
        ldp q30, q31, [sp, #{v30}]
        ldr x8, [sp, #{spsr}]
        and x9, x8, #~(1 << 7)
        msr spsr_el1, x9
        ldr x8, [sp, #{elr}]
        msr elr_el1, x8
        ldp x0, x1, [sp, #{x0}]
        ldp x2, x3, [sp, #{x2}]
        ldp x4, x5, [sp, #{x4}]
        ldp x6, x7, [sp, #{x6}]
        ldp x8, x9, [sp, #{x8}]
        ldp x10, x11, [sp, #{x10}]
        ldp x12, x13, [sp, #{x12}]
        ldp x14, x15, [sp, #{x14}]
        ldp x16, x17, [sp, #{x16}]
        ldp x18, x19, [sp, #{x18}]
        ldp x20, x21, [sp, #{x20}]
        ldp x22, x23, [sp, #{x22}]
        ldp x24, x25, [sp, #{x24}]
        ldp x26, x27, [sp, #{x26}]
        ldp x28, x29, [sp, #{x28}]
        "
    };
}

// FIXME: Use counter to record ISR level.
pub(crate) extern "C" fn is_in_interrupt() -> bool {
    false
}

#[naked]
pub(crate) extern "C" fn init() -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
                mrs x8, mpidr_el1
                and x8, x8, #0Xff
                lsl x8, x8, #14
                sub sp, x1, x8 
                br x2
            "
        )
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

#[inline]
pub extern "C" fn disable_local_irq() {
    unsafe { core::arch::asm!("msr daifset, #3", options(nostack, nomem)) }
}

#[inline]
pub extern "C" fn enable_local_irq() {
    unsafe { core::arch::asm!("msr daifclr, #3", options(nostack, nomem)) }
}

#[inline]
pub extern "C" fn current_cpu_id() -> usize {
    (MPIDR_EL1.get() & 0xff) as usize
}

#[inline(always)]
pub(crate) extern "C" fn idle() {
    unsafe { core::arch::asm!("wfi", options(nostack)) };
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mov {}, sp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old: usize;
    unsafe {
        core::arch::asm!(
            concat!(
                "mrs {}, daif",
                disable_interrupt!(),
            ),
            out(reg) old, options(nostack)
        )
    }
    atomic::compiler_fence(Ordering::SeqCst);
    old
}

#[inline]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    atomic::compiler_fence(Ordering::SeqCst);
    unsafe { core::arch::asm!("msr daif, {}", in(reg) old, options(nostack)) }
}

#[inline]
pub extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!(
            "mrs {}, daif",
            out(reg) x, options(nostack)
        );
    };
    (x & (1 << 7)) == 0
}

#[inline]
pub extern "C" fn pend_switch_context() {}

pub fn secondary_cpu_setup(psci_base: u32) {
    atomic::fence(Ordering::SeqCst);
    for i in 1..blueos_kconfig::CONFIG_NUM_CORES {
        psci::cpu_on(
            psci_base,
            i as usize,
            bluekernel_arch::aarch64_boot_entry as usize,
            0,
        );
    }
}

pub(crate) extern "C" fn send_ipi(target_core_id: usize) {
    let aff1 = 0u64;
    let aff2 = 0u64;
    let aff3 = 0u64;
    let target_list = 1u64 << target_core_id;
    let int_id = 1u64;

    let sgi_val: u64 = (aff3 << 48) | (aff2 << 32) | (int_id << 24) | (aff1 << 16) | (target_list);
    unsafe {
        core::arch::asm!(
            "msr ICC_SGI1R_EL1, {x}",
            "isb",
            x = in(reg) sgi_val,
            options(nomem, nostack)
        );
    }
}
