// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Valentin B. <valentin.be@protonmail.com>

//! Architectural Feature Access Control Register - EL1
//!
//! Controls access to trace, SVE, and Advanced SIMD and floating-point functionality.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CPACR_EL1 [
        /// Traps EL0 and EL1 System register accesses to all implemented trace
        /// registers from both Execution states to EL1, or to EL2 when it is
        /// implemented and enabled in the current Security state and HCR_EL2.TGE
        /// is 1, as follows:
        ///
        /// - In AArch64 state, accesses to trace registers are trapped, reported
        /// using ESR_ELx.EC value 0x18.
        ///
        /// - In AArch32 state, MRC and MCR accesses to trace registers are trapped,
        /// reported using ESR_ELx.EC value 0x05.
        ///
        /// - In AArch32 state, MCR and MCRR accesses to trace registers are trapped,
        /// reported using ESR_ELx.EC value 0x0C.
        ///
        /// System register accesses to the trace registers can have side-effects.
        /// When a System register access is trapped, any side-effects that are
        /// normally associated with the access do not occur before the exception is
        /// taken.
        ///
        /// If System register access to the trace functionality is not implemented,
        /// this bit is considered reserved.
        ///
        /// On a Warm reset, this field resets to an undefined value.
        TTA OFFSET(28) NUMBITS(1) [
            /// This control does not cause any instructions to be trapped.
            NoTrap = 0b0,
            /// This control causes EL0 and EL1 System register accesses to all
            /// implemented trace registers to be trapped.
            TrapTrace = 0b1
        ],

        /// Traps execution at EL0 and EL1 of instructions that access the Advanced SIMD
        /// and floating-point registers from both Execution states to EL1, reported using
        /// ESR_ELx.EC value 0x07, or to EL2 reported using ESR_ELx.EC value 0x00 when EL2
        /// is implemented and enabled in the current Security state and HCR_EL2.TGE is 1,
        /// as follows:
        ///
        /// - In AArch64 state, accesses to FPCR, FPSR, any of the SIMD and floating-point
        /// registers V0-V31, including their views as D0-31 registers or S0-31 registers.
        ///
        /// - In AArch32 state, FPSCR, and any of the SIMD and floating-point registers
        /// Q0-15, including their views as D0-31 registers or S0-31 registers.
        ///
        /// Traps execution at EL1 and EL0 of SVE instructions to EL1, or to EL2 when El2
        /// is implemented and enabled for the current Security state and HCR_EL2.TGE is 1.
        /// The exception is reported using ESR_ELx.EC value 0x07.
        ///
        /// A trap taken as a result of [`CPACR_EL1::ZEN`] has precendence over a trap taken
        /// as a result of [`CPACR_EL1::FPEN`].
        ///
        /// On a Warm reset, this fields resets to an undefined value.
        FPEN OFFSET(20) NUMBITS(2) [
            /// This control causes execution of these instructions at EL0 and EL1 to be trapped.
            TrapEl0El1 = 0b00,
            /// This control causes execution of these instructions at EL0 to be trapped, but
            /// does not cause any instructions at EL1 to be trapped.
            TrapEl0 = 0b01,
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl1El0 = 0b10,
            /// This control does not cause execution of any instructions to be trapped.
            TrapNothing = 0b11
        ],

        /// Traps execution at EL1 and EL0 of SVE instructions and instructions that directly
        /// access the ZCR_EL1 Systme register to EL1, or to EL2 when El2 is implemented in the
        /// current Security state and HCR_EL2.TGE is 1.
        ///
        /// **When FEAT_SVE is implemented:**
        ///
        /// The exception is reported using ESR_ELx.EC value 0x19.
        ///
        /// A trap taken as a result of CPACR_EL1.ZEN has precedence over a trap taken as a result
        /// of CPACR_EL1.FPEN.
        ///
        /// On a Warm reset, this field resets to an undefined value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        ZEN OFFSET(16) NUMBITS(2) [
            /// This control causes execution of these instructions at EL0 and EL1 to be trapped.
            TrapEl0El1 = 0b00,
            /// This control causes execution of these instructions at EL0 to be trapped, but
            /// does not cause execution of any instructions at EL1 to be trapped.
            TrapEl0 = 0b01,
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl1El0 = 0b10,
            /// This control does not cause execution of any instructions to be trapped.
            TrapNothing = 0b11
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CPACR_EL1::Register;

    sys_coproc_read_raw!(u64, "CPACR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CPACR_EL1::Register;

    sys_coproc_write_raw!(u64, "CPACR_EL1", "x");
}

pub const CPACR_EL1: Reg = Reg;
