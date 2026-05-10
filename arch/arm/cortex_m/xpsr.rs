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

//! Cortex-M Program Status Register view (xPSR).
//!
//! xPSR is the architectural combined Program Status Register view. It is made
//! from three mutually exclusive field groups:
//!
//! - APSR: condition and saturation flags produced by instruction execution.
//! - IPSR: the currently active exception number.
//! - EPSR: execution state such as Thumb state and IT/ICI bits.
//!
//! This is a CPU special register read with `MRS`, not a memory-mapped
//! controller register like NVIC, SCB, SysTick, or MPU. The wrapper therefore
//! uses `register_bitfields!` plus `LocalRegisterCopy` to describe a snapshot
//! of the register value while keeping the same typed bitfield style as the
//! MMIO register blocks.
//!
//! See Arm's Cortex-M33 program status register documentation:
//! <https://developer.arm.com/documentation/100235/0100/The-Cortex-M33-Processor/Programmer-s-model/Core-registers/Program-status-registers>

use core::{arch::asm, fmt};

use tock_registers::{register_bitfields, LocalRegisterCopy};

/// xPSR exception number used while executing in Thread mode.
pub const THREAD_MODE_EXCEPTION_NUMBER: u16 = 0;

/// First xPSR exception number assigned to an external interrupt.
pub const EXTERNAL_INTERRUPT_EXCEPTION_BASE: u16 = 16;

register_bitfields! {u32,
    /// Combined Cortex-M Program Status Register view.
    XPSR [
        /// Negative condition flag.
        N OFFSET(31) NUMBITS(1) [],

        /// Zero condition flag.
        Z OFFSET(30) NUMBITS(1) [],

        /// Carry or borrow condition flag.
        C OFFSET(29) NUMBITS(1) [],

        /// Overflow condition flag.
        V OFFSET(28) NUMBITS(1) [],

        /// DSP overflow and saturation flag.
        Q OFFSET(27) NUMBITS(1) [],

        /// Upper IT/ICI/ECI execution state bits.
        IT_ICI_HIGH OFFSET(25) NUMBITS(2) [],

        /// T32 execution state bit.
        T OFFSET(24) NUMBITS(1) [],

        /// Branch target identification state bit.
        B OFFSET(21) NUMBITS(1) [],

        /// Greater-than-or-equal SIMD comparison flags.
        GE OFFSET(16) NUMBITS(4) [],

        /// Lower IT/ICI/ECI execution state bits.
        IT_ICI_LOW OFFSET(10) NUMBITS(6) [],

        /// Current exception number from the IPSR portion of xPSR.
        EXCEPTION_NUMBER OFFSET(0) NUMBITS(9) []
    ]
}

/// Snapshot of the Cortex-M xPSR special register.
///
/// The snapshot is intentionally immutable: reading xPSR observes the current
/// CPU state at one point in time, and field helpers decode that saved value
/// without issuing additional `MRS` instructions.
#[derive(Clone, Copy, Debug)]
pub struct Xpsr {
    register: LocalRegisterCopy<u32, XPSR::Register>,
}

impl Xpsr {
    /// Creates an xPSR snapshot from raw register bits.
    ///
    /// This is useful for decoding the xPSR word stacked by Cortex-M exception
    /// entry, or for tests that want to exercise field decoding without running
    /// on ARM hardware.
    #[inline(always)]
    pub const fn from_bits(bits: u32) -> Self {
        Self {
            register: LocalRegisterCopy::new(bits),
        }
    }

    /// Returns the raw xPSR bits.
    #[inline(always)]
    pub fn bits(self) -> u32 {
        self.register.get()
    }

    /// Returns the current exception number from the IPSR field.
    ///
    /// `0` means Thread mode. Values `1..=15` are core exceptions, and values
    /// starting at `16` identify external interrupts.
    #[inline(always)]
    pub fn exception_number(self) -> u16 {
        self.register.read(XPSR::EXCEPTION_NUMBER) as u16
    }

    /// Returns the external interrupt number if xPSR identifies an IRQ.
    ///
    /// Cortex-M exception numbers include the 16 core exception slots before
    /// external interrupts, so IRQ number `0` is encoded as exception number
    /// `16`.
    #[inline(always)]
    pub fn external_interrupt_number(self) -> Option<u16> {
        self.exception_number()
            .checked_sub(EXTERNAL_INTERRUPT_EXCEPTION_BASE)
    }

    /// Returns the combined IT/ICI/ECI execution-state value.
    ///
    /// Arm splits this execution-state field across two bit ranges. This helper
    /// joins `IT_ICI_HIGH[1:0]` and `IT_ICI_LOW[5:0]` into the architecturally
    /// described 8-bit value.
    #[inline(always)]
    pub fn it_ici(self) -> u8 {
        let high = self.register.read(XPSR::IT_ICI_HIGH) as u8;
        let low = self.register.read(XPSR::IT_ICI_LOW) as u8;
        (high << 6) | low
    }

    /// Returns whether any IT/ICI/ECI execution-state bit is set.
    #[inline(always)]
    pub fn has_it_ici(self) -> bool {
        self.it_ici() != 0
    }

    /// Returns the GE[3:0] comparison flags from APSR.
    ///
    /// These flags are used by SIMD-style comparison instructions on profiles
    /// that implement them. Callers that only care whether any flag is present
    /// can use [`Xpsr::has_ge_flag`].
    #[inline(always)]
    pub fn ge_flags(self) -> u8 {
        self.register.read(XPSR::GE) as u8
    }

    /// Returns whether any GE comparison flag is set.
    #[inline(always)]
    pub fn has_ge_flag(self) -> bool {
        self.ge_flags() != 0
    }

    /// Returns whether the B state bit is set.
    ///
    /// The bit is architecturally defined only on profiles that implement the
    /// corresponding branch-target state. On cores where the bit is reserved,
    /// this simply decodes the snapshot as read.
    #[inline(always)]
    pub fn b(self) -> bool {
        self.register.is_set(XPSR::B)
    }

    /// Returns whether the T32 execution state bit is set.
    ///
    /// Cortex-M executes Thumb instructions. A cleared T bit in an exception
    /// frame is therefore useful diagnostic evidence for an invalid-state fault.
    #[inline(always)]
    pub fn t(self) -> bool {
        self.register.is_set(XPSR::T)
    }

    /// Returns whether the Q saturation flag is set.
    #[inline(always)]
    pub fn q(self) -> bool {
        self.register.is_set(XPSR::Q)
    }

    /// Returns whether the V overflow flag is set.
    #[inline(always)]
    pub fn v(self) -> bool {
        self.register.is_set(XPSR::V)
    }

    /// Returns whether the C carry or borrow flag is set.
    #[inline(always)]
    pub fn c(self) -> bool {
        self.register.is_set(XPSR::C)
    }

    /// Returns whether the Z zero flag is set.
    #[inline(always)]
    pub fn z(self) -> bool {
        self.register.is_set(XPSR::Z)
    }

    /// Returns whether the N negative flag is set.
    #[inline(always)]
    pub fn n(self) -> bool {
        self.register.is_set(XPSR::N)
    }
}

impl Default for Xpsr {
    #[inline(always)]
    fn default() -> Self {
        Self::from_bits(0)
    }
}

/// Reads the Cortex-M xPSR special register.
///
/// # Safety
///
/// The caller must ensure this code is executing on a Cortex-M profile where
/// `mrs xpsr` is a valid instruction and that reading current CPU execution
/// state is appropriate for the surrounding exception or thread context.
#[inline(always)]
pub unsafe fn read() -> Xpsr {
    let bits;
    unsafe {
        asm!(
            "mrs {}, xpsr",
            out(reg) bits,
            options(nomem, nostack, preserves_flags)
        );
    }
    Xpsr::from_bits(bits)
}

impl fmt::Display for Xpsr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "XPSR: 0x{:08x}", self.bits())?;
        writeln!(f, "  Exception Number: {}", self.exception_number())?;

        if self.t() {
            writeln!(f, "  - T32 instruction set")?;
        } else {
            writeln!(f, "  - Invalid state")?;
        }

        writeln!(f, "  B state bit: {}", self.b() as u8)?;
        writeln!(f, "  IT/ICI/ECI flag: {}", self.has_it_ici())?;
        writeln!(f, "  IT/ICI/ECI value: {}", self.it_ici())?;
        writeln!(f, "  GE flags: 0x{:x}", self.ge_flags())?;
        writeln!(f, "  Condition flags:")?;
        writeln!(
            f,
            "    N={} Z={} C={} V={} Q={}",
            self.n() as u8,
            self.z() as u8,
            self.c() as u8,
            self.v() as u8,
            self.q() as u8
        )?;

        Ok(())
    }
}
