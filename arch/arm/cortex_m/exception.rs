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

//! Cortex-M exception stack frame helpers.
//!
//! On exception entry, Cortex-M hardware pushes a basic stack frame containing
//! R0-R3, R12, LR, PC, and xPSR. On hard-float targets, the same type also
//! includes the low floating-point extension frame fields used by the current
//! kernel ABI.
//!
//! See Arm's exception stack frame overview:
//! <https://developer.arm.com/documentation/107706/0100/Exceptions-and-interrupts-overview/Stack-frames>

/// xPSR value required for returning to Thumb state on Cortex-M.
pub const THUMB_MODE_XPSR: usize = 1 << 24;

/// xPSR bit that records hardware-inserted stack alignment padding.
pub const STACK_ALIGNMENT_PADDING: usize = 1 << 9;

/// Initial FPSCR value used when preparing a fresh hard-float thread frame.
#[cfg(target_abi = "eabihf")]
pub const INITIAL_FPSCR: usize = 1 << 25;

/// Sentinel value kept in the reserved word following FPSCR in the current
/// hard-float frame layout.
#[cfg(target_abi = "eabihf")]
pub const INITIAL_FPU_RESERVED: usize = 0xc0dec0de;

/// Registers automatically stacked by Cortex-M exception entry.
///
/// The field order starts with the architectural basic exception frame. On
/// `target_abi = "eabihf"` builds, it also carries the floating-point extension
/// fields after the basic frame to match the kernel's existing hard-float stack
/// layout. Keep this type `repr(C)` because kernel context structures embed it
/// directly and assembly code relies on the resulting memory layout.
#[repr(C, align(8))]
#[derive(Default, Copy, Clone)]
pub struct ExceptionStackFrame {
    /// Argument/result register R0.
    pub r0: usize,
    /// Argument register R1.
    pub r1: usize,
    /// Argument register R2.
    pub r2: usize,
    /// Argument register R3.
    pub r3: usize,
    /// Intra-procedure-call scratch register R12.
    pub r12: usize,
    /// Link register saved by exception entry.
    pub lr: usize,
    /// Program counter restored by exception return.
    pub pc: usize,
    /// Program status register restored by exception return.
    pub xpsr: usize,
    /// Floating-point register S0.
    #[cfg(target_abi = "eabihf")]
    pub s0: usize,
    /// Floating-point register S1.
    #[cfg(target_abi = "eabihf")]
    pub s1: usize,
    /// Floating-point register S2.
    #[cfg(target_abi = "eabihf")]
    pub s2: usize,
    /// Floating-point register S3.
    #[cfg(target_abi = "eabihf")]
    pub s3: usize,
    /// Floating-point register S4.
    #[cfg(target_abi = "eabihf")]
    pub s4: usize,
    /// Floating-point register S5.
    #[cfg(target_abi = "eabihf")]
    pub s5: usize,
    /// Floating-point register S6.
    #[cfg(target_abi = "eabihf")]
    pub s6: usize,
    /// Floating-point register S7.
    #[cfg(target_abi = "eabihf")]
    pub s7: usize,
    /// Floating-point register S8.
    #[cfg(target_abi = "eabihf")]
    pub s8: usize,
    /// Floating-point register S9.
    #[cfg(target_abi = "eabihf")]
    pub s9: usize,
    /// Floating-point register S10.
    #[cfg(target_abi = "eabihf")]
    pub s10: usize,
    /// Floating-point register S11.
    #[cfg(target_abi = "eabihf")]
    pub s11: usize,
    /// Floating-point register S12.
    #[cfg(target_abi = "eabihf")]
    pub s12: usize,
    /// Floating-point register S13.
    #[cfg(target_abi = "eabihf")]
    pub s13: usize,
    /// Floating-point register S14.
    #[cfg(target_abi = "eabihf")]
    pub s14: usize,
    /// Floating-point register S15.
    #[cfg(target_abi = "eabihf")]
    pub s15: usize,
    /// Floating-Point Status and Control Register.
    #[cfg(target_abi = "eabihf")]
    pub fpscr: usize,
    /// Reserved word in the floating-point extension frame.
    #[cfg(target_abi = "eabihf")]
    pub fpu_reserved: usize,
}

impl core::fmt::Debug for ExceptionStackFrame {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "ExceptionStackFrame {{")?;
        write!(f, "r0: 0x{:x} ", self.r0)?;
        write!(f, "r1: 0x{:x} ", self.r1)?;
        write!(f, "r2: 0x{:x} ", self.r2)?;
        write!(f, "r3: 0x{:x} ", self.r3)?;
        write!(f, "r12: 0x{:x} ", self.r12)?;
        write!(f, "lr: 0x{:x} ", self.lr)?;
        write!(f, "pc: 0x{:x} ", self.pc)?;
        write!(f, "xpsr: 0x{:x}", self.xpsr)?;
        #[cfg(target_abi = "eabihf")]
        {
            write!(f, " fpscr: 0x{:x}", self.fpscr)?;
            write!(f, " fpu_reserved: 0x{:x}", self.fpu_reserved)?;
        }
        write!(f, "}}")
    }
}

impl ExceptionStackFrame {
    /// Borrows a Cortex-M exception frame from a stack pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure `sp` is non-null, correctly aligned, and points
    /// to a complete Cortex-M exception frame for the returned lifetime.
    /// The caller must also ensure no mutable reference aliases the same frame
    /// while the returned shared reference is alive.
    #[inline(always)]
    pub unsafe fn from_stack_pointer<'a>(sp: *const usize) -> &'a Self {
        unsafe { &*(sp as *const Self) }
    }

    /// Mutably borrows a Cortex-M exception frame from a stack pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure `sp` is non-null, correctly aligned, and points
    /// to a complete Cortex-M exception frame for the returned lifetime.
    /// The caller must also have exclusive access to that frame while the
    /// returned mutable reference is alive.
    #[inline(always)]
    pub unsafe fn from_stack_pointer_mut<'a>(sp: *mut usize) -> &'a mut Self {
        unsafe { &mut *(sp as *mut Self) }
    }

    /// Sets the return PC restored by exception return.
    ///
    /// # Safety
    ///
    /// The caller must ensure this frame will be consumed as a valid Cortex-M
    /// exception-return frame and that `pc` points to executable Thumb code.
    #[inline(always)]
    pub unsafe fn set_return_address(&mut self, pc: usize) -> &mut Self {
        self.pc = pc;
        self
    }

    /// Returns the PC restored by exception return.
    ///
    /// # Safety
    ///
    /// The caller must ensure this value is interpreted in the context of a
    /// valid Cortex-M exception stack frame.
    #[inline(always)]
    pub unsafe fn return_address(&self) -> usize {
        self.pc
    }

    /// Sets one of the four register arguments in R0-R3.
    ///
    /// # Safety
    ///
    /// The caller must ensure mutating the stacked argument register preserves
    /// the function ABI expected when the frame is restored.
    ///
    /// # Panics
    ///
    /// Panics if `i` is not in `0..4`. Additional arguments must be passed by
    /// stack according to the AAPCS calling convention.
    #[inline(always)]
    pub unsafe fn set_arg(&mut self, i: usize, val: usize) -> &mut Self {
        match i {
            0 => self.r0 = val,
            1 => self.r1 = val,
            2 => self.r2 = val,
            3 => self.r3 = val,
            _ => panic!("Should be passed by stack"),
        }
        self
    }

    /// Initializes xPSR for a fresh Thread-mode exception return frame.
    ///
    /// # Safety
    ///
    /// The caller must ensure this frame is being prepared for a fresh
    /// Cortex-M Thread-mode start and that other frame fields are initialized
    /// consistently before exception return consumes it.
    #[inline(always)]
    pub unsafe fn init_thread_mode(&mut self) -> &mut Self {
        self.xpsr = THUMB_MODE_XPSR;
        #[cfg(target_abi = "eabihf")]
        {
            self.fpscr = INITIAL_FPSCR;
            self.fpu_reserved = INITIAL_FPU_RESERVED;
        }
        self
    }

    /// Clears the stacked xPSR alignment-padding marker.
    ///
    /// When duplicating or rewriting an exception frame, clearing this bit keeps
    /// the copied frame from describing padding that is not present in the new
    /// stack location.
    ///
    /// # Safety
    ///
    /// The caller must ensure the copied frame really is being placed at a
    /// stack location without the hardware alignment padding described by the
    /// original xPSR bit.
    #[inline(always)]
    pub unsafe fn clear_stack_alignment_padding(&mut self) -> &mut Self {
        self.xpsr &= !STACK_ALIGNMENT_PADDING;
        self
    }

    /// Returns a copy of the stacked xPSR with the alignment-padding marker
    /// cleared.
    ///
    /// # Safety
    ///
    /// The caller must ensure the returned value is used only when duplicating
    /// or rewriting a frame at a stack location that does not include the
    /// original hardware-inserted alignment padding.
    #[inline(always)]
    pub unsafe fn xpsr_without_stack_alignment_padding(&self) -> usize {
        self.xpsr & !STACK_ALIGNMENT_PADDING
    }
}
