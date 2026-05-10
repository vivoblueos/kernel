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

//! Safe Cortex-M policy layer for BlueOS.
//!
//! This module is the public boundary consumed by the kernel. Functions exposed
//! here keep the old kernel-facing contract as safe C-ABI helpers, while the
//! raw assembly and register accessors stay in submodules such as [`asm`],
//! [`scb`], [`nvic`], [`systick`], and [`mpu`]. That split lets kernel code
//! re-export these helpers directly without spreading `unsafe` through normal
//! scheduler, interrupt, and debug paths.

pub mod asm;
pub mod exception;
pub mod hardfault;
pub mod irq;
pub mod mpu;
pub mod nvic;
pub mod scb;
pub mod systick;
pub mod xpsr;

pub use exception::{ExceptionStackFrame, THUMB_MODE_XPSR};

use core::sync::atomic::{compiler_fence, Ordering};

// Keep the Cortex-M architectural exception slots in bluekernel_arch rather
// than rebuilding the same fixed layout in the kernel. The kernel still
// provides the handlers with OS semantics (`_start`, SVC, PendSV, SysTick),
// while this table preserves the previous vector order and zero-filled
// reserved entries.
core::arch::global_asm!(
    r#"
    .section .exception.handlers, "a", %progbits
    .balign 4
    .global __EXCEPTION_HANDLERS__
    .type __EXCEPTION_HANDLERS__, %object
__EXCEPTION_HANDLERS__:
    .word _start
    .word handle_nmi
    .word bk_handle_hardfault
    .word handle_memfault
    .word handle_busfault
    .word handle_usagefault
    .word 0
    .word 0
    .word 0
    .word 0
    .word handle_svc
    .word 0
    .word 0
    .word handle_pendsv
    .word handle_systick
    .size __EXCEPTION_HANDLERS__, . - __EXCEPTION_HANDLERS__
    "#
);

/// BASEPRI threshold used to mask local scheduler-level interrupts.
#[cfg(irq_priority_bits_2)]
pub const LOCAL_IRQ_BASEPRI: usize = 0x80;
/// BASEPRI threshold used to mask local scheduler-level interrupts.
#[cfg(irq_priority_bits_3)]
pub const LOCAL_IRQ_BASEPRI: usize = 0x40;
/// BASEPRI threshold used to mask local scheduler-level interrupts.
#[cfg(irq_priority_bits_8)]
pub const LOCAL_IRQ_BASEPRI: usize = 0x20;

/// Complete saved thread context for Cortex-M exception return.
///
/// The context begins with software-saved callee registers and ends with the
/// hardware exception stack frame. On hard-float builds, the same type expands
/// with the high floating-point callee-saved registers S16-S31 before the
/// exception frame. Keeping this as one `repr(C)` type with ABI-gated fields
/// matches [`ExceptionStackFrame`] and makes the non-float and hard-float ABI
/// variants share one API surface.
#[repr(C, align(8))]
#[derive(Default, Debug, Copy, Clone)]
pub struct Context {
    /// Callee-saved register R4.
    pub r4: usize,
    /// Callee-saved register R5.
    pub r5: usize,
    /// Callee-saved register R6.
    pub r6: usize,
    /// Callee-saved register R7.
    pub r7: usize,
    /// Callee-saved register R8.
    pub r8: usize,
    /// Callee-saved register R9.
    pub r9: usize,
    /// Callee-saved register R10.
    pub r10: usize,
    /// Callee-saved register R11.
    pub r11: usize,
    /// Floating-point callee-saved register S16.
    #[cfg(target_abi = "eabihf")]
    pub s16: usize,
    /// Floating-point callee-saved register S17.
    #[cfg(target_abi = "eabihf")]
    pub s17: usize,
    /// Floating-point callee-saved register S18.
    #[cfg(target_abi = "eabihf")]
    pub s18: usize,
    /// Floating-point callee-saved register S19.
    #[cfg(target_abi = "eabihf")]
    pub s19: usize,
    /// Floating-point callee-saved register S20.
    #[cfg(target_abi = "eabihf")]
    pub s20: usize,
    /// Floating-point callee-saved register S21.
    #[cfg(target_abi = "eabihf")]
    pub s21: usize,
    /// Floating-point callee-saved register S22.
    #[cfg(target_abi = "eabihf")]
    pub s22: usize,
    /// Floating-point callee-saved register S23.
    #[cfg(target_abi = "eabihf")]
    pub s23: usize,
    /// Floating-point callee-saved register S24.
    #[cfg(target_abi = "eabihf")]
    pub s24: usize,
    /// Floating-point callee-saved register S25.
    #[cfg(target_abi = "eabihf")]
    pub s25: usize,
    /// Floating-point callee-saved register S26.
    #[cfg(target_abi = "eabihf")]
    pub s26: usize,
    /// Floating-point callee-saved register S27.
    #[cfg(target_abi = "eabihf")]
    pub s27: usize,
    /// Floating-point callee-saved register S28.
    #[cfg(target_abi = "eabihf")]
    pub s28: usize,
    /// Floating-point callee-saved register S29.
    #[cfg(target_abi = "eabihf")]
    pub s29: usize,
    /// Floating-point callee-saved register S30.
    #[cfg(target_abi = "eabihf")]
    pub s30: usize,
    /// Floating-point callee-saved register S31.
    #[cfg(target_abi = "eabihf")]
    pub s31: usize,
    /// Hardware-stacked exception frame restored by exception return.
    pub exception_frame: ExceptionStackFrame,
}

impl core::ops::Deref for Context {
    type Target = ExceptionStackFrame;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.exception_frame
    }
}

impl core::ops::DerefMut for Context {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.exception_frame
    }
}

impl Context {
    /// Sets the return PC restored when this context exits the exception.
    #[inline(always)]
    pub fn set_return_address(&mut self, pc: usize) -> &mut Self {
        unsafe {
            self.exception_frame.set_return_address(pc);
        }
        self
    }

    /// Returns the PC restored when this context exits the exception.
    #[inline(always)]
    pub fn get_return_address(&self) -> usize {
        unsafe { self.exception_frame.return_address() }
    }

    /// Sets one of the first four argument registers in the embedded frame.
    #[inline(always)]
    pub fn set_arg(&mut self, i: usize, val: usize) -> &mut Self {
        unsafe {
            self.exception_frame.set_arg(i, val);
        }
        self
    }

    /// Initializes the embedded exception frame for a fresh Thread-mode start.
    #[inline(always)]
    pub fn init(&mut self) -> &mut Self {
        unsafe {
            self.exception_frame.init_thread_mode();
        }
        self
    }
}

/// Clears BASEPRI so locally masked interrupts can run again.
#[inline(always)]
pub extern "C" fn enable_local_irq() {
    unsafe { asm::write_basepri(0) }
}

/// Raises BASEPRI to the local interrupt mask and synchronizes the instruction
/// stream.
#[inline(always)]
pub extern "C" fn disable_local_irq() {
    unsafe {
        asm::write_basepri(LOCAL_IRQ_BASEPRI);
        asm::isb();
    }
}

/// Raises BASEPRI and returns the previous local interrupt mask.
#[inline(always)]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old = unsafe { asm::read_basepri() };
    unsafe {
        asm::write_basepri(LOCAL_IRQ_BASEPRI);
        asm::isb();
    }
    compiler_fence(Ordering::SeqCst);
    old
}

/// Restores a BASEPRI value returned by `disable_local_irq_save`.
#[inline(always)]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    compiler_fence(Ordering::SeqCst);
    unsafe { asm::write_basepri(old) }
}

/// Returns whether the BASEPRI local interrupt mask is disabled.
#[inline(always)]
pub extern "C" fn local_irq_enabled() -> bool {
    unsafe { asm::read_basepri() == 0 }
}

/// Enters idle by waiting for the next interrupt.
#[inline(always)]
pub extern "C" fn idle() {
    unsafe { asm::wfi() }
}

/// Returns the currently selected stack pointer.
#[inline(always)]
pub extern "C" fn current_sp() -> usize {
    unsafe { asm::read_sp() }
}

/// Returns the Main Stack Pointer.
#[inline(always)]
pub extern "C" fn current_msp() -> usize {
    unsafe { asm::read_msp() }
}

/// Returns the Process Stack Pointer.
#[inline(always)]
pub extern "C" fn current_psp() -> usize {
    unsafe { asm::read_psp() }
}

/// Returns whether the CPU is currently handling an exception.
#[inline(always)]
pub extern "C" fn is_in_interrupt() -> bool {
    unsafe { scb::is_in_exception() }
}
