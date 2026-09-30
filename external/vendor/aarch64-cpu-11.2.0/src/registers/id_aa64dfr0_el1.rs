// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! AArch64 Debug Feature Register 0 - EL1
//!
//! Provides top level information about the debug system in AArch64 state.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub ID_AA64DFR0_EL1 [
        /// Branch Record Buffer Extension.
        ///
        /// - 0000 Branch Record Buffer Extension not implemented.
        /// - 0001 Branch Record Buffer Extension implemented.
        /// - 0010 As 0b0001, and adds support for branch recording at EL3.
        ///
        /// All other values are reserved.
        BRBE OFFSET(52) NUMBITS(4) [
            NotImplemented = 0b0000,
            Implemented = 0b0001,
            Implemented_El3Support = 0b0010,
        ],

        /// Multi-threaded PMU extension.
        ///
        /// - 0000 FEAT_MTPMU not implemented. If FEAT_PMUv3 is implemented, it is IMPLEMENTATION
        ///        DEFINED whether PMEVTYPER<n>_EL0.MT and PMEVTYPER<n>.MT are read/write or RES0.
        /// - 0001 FEAT_MTPMU and FEAT_PMUv3 implemented. PMEVTYPER<n>_EL0.MT and PMEVTYPER<n>.MT
        ///        are read/write. When FEAT_MTPMU is disabled, the Effective values of
        ///        PMEVTYPER<n>_EL0.MT and PMEVTYPER<n>.MT are 0.
        /// - 1111 FEAT_MTPMU not implemented. If FEAT_PMUv3 is implemented, PMEVTYPER<n>_EL0.MT
        ///        and PMEVTYPER<n>.MT are RES0.
        ///
        /// All other values are reserved.
        MTPMU OFFSET(48) NUMBITS(4) [
            NotImplemented = 0b0000,
            Implemented = 0b0001,
            NotImplemented_Res0 = 0b1111,
        ],

        /// Trace Buffer Extension.
        ///
        /// - 0000 Trace Buffer Extension not implemented.
        /// - 0001 Trace Buffer Extension implemented.
        /// - 0010 As 0b0001, and adds:
        ///   - If EL2 and FEAT_FGT are implemented, a fine-grained trap on the TSB CSYNC instruction.
        ///   - If EL2 is implemented, an EL2 control to override TRBLIMITR_EL1.nVM.
        ///   - The TRBE Profiling exception extension, FEAT_TRBE_EXC.
        ///
        /// All other values are reserved.
        TraceBuffer OFFSET(44) NUMBITS(4) [
            NotImplemented = 0b0000,
            Implemented = 0b0001,
            Implemented_Trbe = 0b0010,
        ],

        /// Armv8.4 Self-hosted Trace Extension version.
        TraceFilt OFFSET(40) NUMBITS(4) [
            NotImplemented = 0b0000,
            Implemented = 0b0001,
        ],

        /// Statistical Profiling Extension version.
        PMSVer OFFSET(32) NUMBITS(4) [],

        /// Number of context-aware breakpoints, minus 1.
        CTX_CMPs OFFSET(28) NUMBITS(4) [],

        /// Number of watchpoints, minus 1.
        WRPs OFFSET(20) NUMBITS(4) [],

        /// Number of breakpoints, minus 1.
        BRPs OFFSET(12) NUMBITS(4) [],

        /// Performance Monitors Extension version.
        PMUVer OFFSET(8) NUMBITS(4) [],

        /// Trace support. Indicates whether System register interface to a trace unit is
        /// implemented.
        TraceVer OFFSET(4) NUMBITS(4) [],

        /// Debug architecture version. Indicates presence of Armv8 debug architecture.
        DebugVer OFFSET(0) NUMBITS(4) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ID_AA64DFR0_EL1::Register;

    sys_coproc_read_raw!(u64, "ID_AA64DFR0_EL1", "x");
}

pub const ID_AA64DFR0_EL1: Reg = Reg {};
