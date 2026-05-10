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

//! Small Cortex-M assembly instruction wrappers.
//!
//! This module follows the shape of `cortex_m::asm` for simple architectural
//! instructions, while keeping Bluekernel-specific safety contracts explicit:
//! <https://github.com/rust-embedded/cortex-m/blob/master/cortex-m/src/asm.rs>
//!
//! It intentionally contains only reusable CPU instructions and special-register
//! accessors. Larger naked assembly routines that depend on the kernel's
//! `Context` layout, exception-frame layout, or scheduler calling convention
//! remain in `kernel/src/arch/arm`.
//!
//! See also:
//! - CMSIS-Core register access helpers for MSP, PSP, and BASEPRI:
//!   <https://arm-software.github.io/CMSIS_6/main/Core/group__Core__Register__gr.html>
//! - Arm Cortex-M memory barrier guidance:
//!   <https://documentation-service.arm.com/static/5efefb97dbdee951c1cd5aaf>

use core::arch::asm;

/// A no-operation instruction.
///
/// # Safety
///
/// The caller must ensure that executing a Cortex-M `nop` instruction is valid
/// in the current target and execution context.
#[inline(always)]
pub unsafe fn nop() {
    unsafe {
        asm!("nop", options(nomem, nostack, preserves_flags));
    }
}

/// Waits for an interrupt.
///
/// # Safety
///
/// The caller must ensure that entering sleep until an interrupt is compatible
/// with the current interrupt state and platform power-management rules. If
/// preceding memory-mapped writes must complete before sleep, issue `dsb()`
/// first as required by the platform.
#[inline(always)]
pub unsafe fn wfi() {
    unsafe {
        asm!("wfi", options(nomem, nostack, preserves_flags));
    }
}

/// Waits for an event.
///
/// # Safety
///
/// The caller must ensure that entering event-wait state is valid for the
/// current kernel and platform state.
#[inline(always)]
pub unsafe fn wfe() {
    unsafe {
        asm!("wfe", options(nomem, nostack, preserves_flags));
    }
}

/// Sends an event to wake processors waiting in `wfe`.
///
/// # Safety
///
/// The caller must ensure that signaling an event is valid for the platform's
/// synchronization protocol.
#[inline(always)]
pub unsafe fn sev() {
    unsafe {
        asm!("sev", options(nomem, nostack, preserves_flags));
    }
}

/// Instruction Synchronization Barrier.
///
/// ISB flushes the pipeline so instructions after the barrier are fetched and
/// executed using the effects of context-changing operations before it.
///
/// # Safety
///
/// The caller must ensure that executing an ISB is valid in the current
/// Cortex-M context.
#[inline(always)]
pub unsafe fn isb() {
    unsafe {
        asm!("isb", options(nomem, nostack, preserves_flags));
    }
}

/// Data Synchronization Barrier.
///
/// DSB waits until memory accesses before the barrier have completed before
/// subsequent instructions continue.
///
/// # Safety
///
/// The caller must ensure that executing a DSB is valid in the current
/// Cortex-M context.
#[inline(always)]
pub unsafe fn dsb() {
    unsafe {
        asm!("dsb", options(nomem, nostack, preserves_flags));
    }
}

/// Data Memory Barrier.
///
/// DMB orders memory accesses before and after the barrier without requiring
/// all preceding accesses to complete.
///
/// # Safety
///
/// The caller must ensure that executing a DMB is valid in the current
/// Cortex-M context.
#[inline(always)]
pub unsafe fn dmb() {
    unsafe {
        asm!("dmb", options(nomem, nostack, preserves_flags));
    }
}

/// Disables maskable interrupts by setting PRIMASK.I.
///
/// # Safety
///
/// The caller must preserve kernel interrupt-state invariants. Bluekernel
/// normally uses BASEPRI for local critical sections, so this should be
/// reserved for early boot or architecture code that really needs PRIMASK.
#[inline(always)]
pub unsafe fn cpsid_i() {
    unsafe {
        asm!("cpsid i", options(nomem, nostack, preserves_flags));
    }
}

/// Enables maskable interrupts by clearing PRIMASK.I.
///
/// # Safety
///
/// The caller must ensure all required exception handlers and interrupt
/// priorities are initialized before interrupts can run.
#[inline(always)]
pub unsafe fn cpsie_i() {
    unsafe {
        asm!("cpsie i", options(nomem, nostack, preserves_flags));
    }
}

/// Reads the currently selected stack pointer.
///
/// In Thread mode this is selected by CONTROL.SPSEL. In Handler mode it is the
/// main stack pointer.
///
/// # Safety
///
/// The caller must ensure that observing the current stack pointer does not
/// violate any calling-convention or diagnostic assumptions.
#[inline(always)]
pub unsafe fn read_sp() -> usize {
    let value: usize;
    unsafe {
        asm!("mov {}, sp", out(reg) value, options(nomem, nostack, preserves_flags));
    }
    value
}

/// Reads the Main Stack Pointer (MSP).
///
/// # Safety
///
/// The caller must ensure the instruction is executed on Cortex-M and that the
/// returned pointer is interpreted only according to the current CPU mode.
#[inline(always)]
pub unsafe fn read_msp() -> usize {
    let value: usize;
    unsafe {
        asm!("mrs {}, msp", out(reg) value, options(nomem, nostack, preserves_flags));
    }
    value
}

/// Writes the Main Stack Pointer (MSP).
///
/// # Safety
///
/// The caller must provide a valid, correctly aligned stack pointer for the
/// current exception and boot state. An invalid MSP can make exception entry,
/// return, or fault handling immediately undefined.
#[inline(always)]
pub unsafe fn write_msp(value: usize) {
    unsafe {
        asm!("msr msp, {}", in(reg) value, options(nomem, nostack, preserves_flags));
    }
}

/// Reads the Process Stack Pointer (PSP).
///
/// # Safety
///
/// The caller must ensure the PSP is meaningful for the current execution
/// state. PSP is typically used by OS thread mode code.
#[inline(always)]
pub unsafe fn read_psp() -> usize {
    let value: usize;
    unsafe {
        asm!("mrs {}, psp", out(reg) value, options(nomem, nostack, preserves_flags));
    }
    value
}

/// Writes the Process Stack Pointer (PSP).
///
/// # Safety
///
/// The caller must provide a valid, correctly aligned process stack pointer for
/// the thread or exception-return path that will consume it.
#[inline(always)]
pub unsafe fn write_psp(value: usize) {
    unsafe {
        asm!("msr psp, {}", in(reg) value, options(nomem, nostack, preserves_flags));
    }
}

/// Reads BASEPRI, the Cortex-M priority threshold mask.
///
/// # Safety
///
/// The caller must ensure the returned raw priority threshold is interpreted
/// using the target's implemented priority bits.
#[inline(always)]
pub unsafe fn read_basepri() -> usize {
    let value: usize;
    unsafe {
        asm!("mrs {}, basepri", out(reg) value, options(nomem, nostack, preserves_flags));
    }
    value
}

/// Writes BASEPRI, the Cortex-M priority threshold mask.
///
/// Writing `0` disables the BASEPRI mask. Non-zero values mask interrupts with
/// equal or lower urgency according to the target's implemented priority bits.
///
/// # Safety
///
/// The caller must preserve Bluekernel's priority invariants. Raising or
/// clearing BASEPRI at the wrong point can break critical sections or allow an
/// interrupt to observe partially updated scheduler state.
#[inline(always)]
pub unsafe fn write_basepri(value: usize) {
    unsafe {
        asm!("msr basepri, {}", in(reg) value, options(nomem, nostack, preserves_flags));
    }
}

/// Resets MSP/PSP and enters the first scheduled thread-mode continuation.
///
/// This is the non-returning bootstrap sequence used after the kernel has
/// chosen the first process stack. It updates both stack pointers, restores the
/// minimal architectural state expected by the continuation, masks lower
/// priority interrupts with BASEPRI, enables PRIMASK-controlled interrupts,
/// and branches to `cont`.
///
/// The operation stays in one inline-assembly block so the compiler cannot use
/// the old stack after MSP has been replaced. This mirrors the previous kernel
/// inline assembly while moving the reusable Cortex-M register writes into the
/// architecture crate.
///
/// # Safety
///
/// The caller must ensure:
///
/// - `msp` points to a valid main stack for exception handling.
/// - `psp` points to a valid process stack for the first scheduled thread.
/// - `xpsr`, `control`, and `basepri` are valid architectural values for the
///   target and kernel interrupt policy.
/// - `cont` is a valid executable continuation and must not return.
#[inline(always)]
pub unsafe fn reset_stack_pointers_and_start(
    msp: *mut u8,
    psp: usize,
    xpsr: usize,
    control: usize,
    basepri: usize,
    cont: extern "C" fn() -> !,
) -> ! {
    unsafe {
        asm!(
            "
            msr psp, {psp}
            msr msp, {msp}
            ",
            "
            msr xpsr, {xpsr}
            msr control, {control}
            ldr lr, =0
            msr basepri, {basepri}
            cpsie i
            bx {cont}
            ",
            options(nostack, noreturn),
            msp = in(reg) msp,
            psp = in(reg) psp,
            xpsr = in(reg) xpsr,
            control = in(reg) control,
            basepri = in(reg) basepri,
            cont = in(reg) cont,
        )
    }
}
