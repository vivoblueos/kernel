// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Callum Thomson <callumthom11@gmail.com>

//! Monitor Debug Configuration Register - EL2
//!
//! Configuration options for self-hosted debug and Performance Monitors for EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub MDCR_EL2 [
        /// EnSTEPOP.
        ///
        /// Requires FEAT_STEP2
        ///
        /// Enables execution from MDSTEPOP_EL1.
        EnSTEPOP OFFSET(50) NUMBITS(1) [],

        /// Extended Breakpoint and Watchpoint Enable.
        ///
        /// Requires FEAT_Debugv8p9
        EBWE OFFSET(43) NUMBITS(1) [],

        /// Performance Monitors Exception Enable.
        ///
        /// Requires FEAT_EBEP
        PMEE OFFSET(40) NUMBITS(2) [
            AssertOnOverflowAndDisabled = 0b00,
            ControlledByPMECR = 0b01,
            DeassertedAndDisabled = 0b10,
            DeassertedAndEnabled = 0b11,
        ],

        /// Hypervisor Performance Monitors Freeze-On-SPE.
        ///
        /// Requires FEAT_SPEv1p2
        HPMFZS OFFSET(36) NUMBITS(1) [],

        /// Performance Monitors Snapshot Enable.
        ///
        /// Requires FEAT_PMUv3_SS
        PMSSE OFFSET(30) NUMBITS(2) [
            Disabled = 0b00,
            ControlledByPMECR = 0b01,
            EnabledAndProhibited = 0b10,
            EnabledAndAllowed = 0b11,
        ],

        /// Hypervisor Performance Monitors Freeze-On-Overflow.
        ///
        /// Requires FEAT_PMUv3p7
        HPMFZO OFFSET(29) NUMBITS(1) [],

        /// Multi-Threaded PMU Enable.
        ///
        /// Requires FEAT_MTPMU implemented, requires EL3 _not_ implemented
        MTPME OFFSET(28) NUMBITS(1) [],

        /// Trap Debug Comms Channel.
        ///
        /// Requires FEAT_FGT
        ///
        /// Traps access to DCC registers.
        TDCC OFFSET(27) NUMBITS(1) [],

        /// Hypervisor Long Event Counter Enable.
        ///
        /// Requires FEAT_PMUv3p5
        HLP OFFSET(26) NUMBITS(1) [],

        /// EL2 Trace Buffer.
        ///
        /// Requires FEAT_TRBE
        ///
        /// Controls the owning exception level of the Trace Buffer.
        E2TB OFFSET(24) NUMBITS(2) [
            EL1OrEL2OwnerTrapToEL2 = 0b00,
            EL1OwnerTrapToEL2 = 0b10,
            EL1OwnerNotTrapped = 0b11,
        ],

        /// Hypervisor Cycle Counter Disable.
        ///
        /// Requires FEAT_PMUv3p5
        ///
        /// Stops PMCCNTR_EL0 from counting at EL2.
        HCCD OFFSET(23) NUMBITS(1) [],

        /// TTRF.
        ///
        /// Requires FEAT_TRF
        ///
        /// Traps access to Trace Filter Control registers at EL1.
        TTRF OFFSET(19) NUMBITS(1) [],

        /// HPMD.
        ///
        /// Requires FEAT_PMUv3p1, meaning changes when FEAT_Debugv8p2 is also implemented
        ///
        /// Controls access to guets performance monitors.
        HPMD OFFSET(17) NUMBITS(1) [],

        /// EnSPM.
        ///
        /// Requires FEAT_SPMU
        ///
        /// Enable access to PMU registers.
        EnSPM OFFSET(15) NUMBITS(1) [],

        /// Trap Performance Monitor Sampling.
        ///
        /// Requires FEAT_SPE
        ///
        /// Trap access to SPE registers.
        TPMS OFFSET(14) NUMBITS(1) [],

        /// EL2 Profiling Buffer.
        ///
        /// Requires FEAT_SPE
        ///
        /// Controls the owning exception level.
        E2PB OFFSET(12) NUMBITS(2) [
            OwnedByEL2OrEL1 = 0b00,
            TrapToEL2 = 0b10,
            OwnedByEL1 = 0b11,
        ],

        /// TDRA.
        ///
        /// Trap access to Debug ROM Address registers.
        TDRA OFFSET(11) NUMBITS(1) [],

        /// TDOSA.
        ///
        /// Requires FEAT_DoubleLock
        ///
        /// Trap access to OS related registers.
        TDOSA OFFSET(10) NUMBITS(1) [],

        /// TDA.
        ///
        /// Trap access to debug registers.
        TDA OFFSET(9) NUMBITS(1) [],

        /// Trap Debug Exceptions.
        ///
        /// Controls the routing of Debug exceptions
        TDE OFFSET(8) NUMBITS(1) [
            RouteToEL1 = 0,
            RouteToEL2Or1 = 1
        ],

        /// Hyp Enable.
        ///
        /// Requires FEAT_PMUv3
        HPME OFFSET(7) NUMBITS(1) [],

        /// Trap PMU registers.
        ///
        /// Requires FEAT_PMUv3
        ///
        /// Trap accesses to PMU registers to EL2.
        TPM OFFSET(6) NUMBITS(1) [],

        /// Trap PMCR registers.
        ///
        /// Requires FEAT_PMUv3
        ///
        /// Trap accesses to PMCR_EL0 to EL2.
        TPMCR OFFSET(5) NUMBITS(1) [],

        /// HPMN.
        ///
        /// Controls the number of event counter and event counter snapshot registers.
        HPMN OFFSET(0) NUMBITS(5) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = MDCR_EL2::Register;

    sys_coproc_read_raw!(u64, "MDCR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = MDCR_EL2::Register;

    sys_coproc_write_raw!(u64, "MDCR_EL2", "x");
}

pub const MDCR_EL2: Reg = Reg {};
