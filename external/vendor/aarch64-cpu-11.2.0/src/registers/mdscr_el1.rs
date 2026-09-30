// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Callum Thomson <callumthom11@gmail.com>

//! Monitor Debug System Control Register - EL1
//!
//! Main control register for debug functions.
//!
//! This register is present only when FEAT_AA64 is implemented. Otherwise, direct accesses to MDSCR_EL1 are UNDEFINED.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub MDSCR_EL1 [
        /// Software step control bit.
        ///
        /// Enables execution from MDSTEPOP_EL1
        ///
        /// Requires FEAT_STEP2 to be implemented.
        EnSTEPOP OFFSET(50) NUMBITS(1) [],

        /// Extended Halting Breakpoint and Watchpoint Enable.
        EHBWE OFFSET(35) NUMBITS(1) [],

        /// Enable use of System PMU registers.
        EnSPM OFFSET(34) NUMBITS(1) [
            TrapSystemPMUAccess = 0,
            AllowSystemPMUAccess = 1,
        ],

        /// Trap Trace Accesses.
        TTA OFFSET(33) NUMBITS(1) [],

        /// Extended Monitor Breakpoint and Watchpoint Enable.
        EMBWE OFFSET(32) NUMBITS(1) [],

        /// Trace Filter Override.
        TFO OFFSET(31) NUMBITS(1) [],

        /// RXfull.
        ///
        /// Used to save and restore the value of EDSCR.RXfull.
        RXfull OFFSET(30) NUMBITS(1) [],

        /// TXfull.
        ///
        /// Used to save and restore the value of EDSCR.TXfull.
        TXfull OFFSET(29) NUMBITS(1) [],

        /// RXO.
        ///
        /// Used to save and restore the value of EDSCR.RXO.
        RXO OFFSET(27) NUMBITS(1) [],

        /// TXU.
        ///
        /// Used to save and restore the value of EDSCR.TXU.
        TXU OFFSET(26) NUMBITS(1) [],

        /// INTdis.
        ///
        /// Used to save and restore the value of EDSCR.INTdis.
        INTdis OFFSET(22) NUMBITS(2) [],

        /// TDA.
        ///
        /// Used to save and restore the value of EDSCR.TDA.
        TDA OFFSET(21) NUMBITS(1) [],

        /// SC2.
        ///
        /// Requires FEAT_PCSRv8, FEAT_VHE to be implemented and FEAT_PCRv8p2 to not be
        /// implemented.
        ///
        /// Used to save and restore the value of EDSCR.SC2.
        SC2 OFFSET(19) NUMBITS(1) [],

        /// Monitor Debug Events.
        ///
        /// Enables Breakpoint, Watchpoint and Vector Catch exceptions.
        MDE OFFSET(15) NUMBITS(1) [],

        /// HDE.
        ///
        /// Used to save and restore the value of EDSCR.HDE.
        HDE OFFSET(14) NUMBITS(1) [],

        /// Local (kernel) debug enable.
        ///
        /// Enables Debug Exceptions within EL_D when using AArch64
        /// RES0 if EL_D is AArch32
        KDE OFFSET(13) NUMBITS(1) [
            OnlyBreakpointInstructionsEnabled = 0,
            AllDebugExceptionsEnabled = 1,
        ],

        /// Trap DCC register access.
        ///
        /// Traps access to the Debug Communication Channel (DCC) registers from EL0 to higher
        /// exception level.
        TDCC OFFSET(12) NUMBITS(1) [],

        /// ERR.
        ///
        /// Used to save and restore the value of EDSCR.ERR.
        ERR OFFSET(6) NUMBITS(1) [],

        /// Software step.
        ///
        /// Enable software step if EL_D is using AArch64
        /// RES0 if EL_D is using AArch32
        SS OFFSET(0) NUMBITS(1) [
            SoftwareStepDisabled = 0,
            SoftwareStepEnabled = 1,
        ],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = MDSCR_EL1::Register;

    sys_coproc_read_raw!(u64, "MDSCR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = MDSCR_EL1::Register;

    sys_coproc_write_raw!(u64, "MDSCR_EL1", "x");
}

pub const MDSCR_EL1: Reg = Reg {};
