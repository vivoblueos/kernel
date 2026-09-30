// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! AArch64 Instruction Set Attribute Register 1 - EL1
//!
//! Provides information about the features and instructions implemented in AArch64 state.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub ID_AA64ISAR1_EL1 [
        /// Indicates support for an IMPLEMENTATION DEFINED algorithm is implemented in the PE for
        /// generic code authentication in AArch64 state.
        GPI OFFSET(28) NUMBITS(4) [
            NotSupported = 0b0000,
            Supported = 0b0001
        ],

        /// Indicates whether the QARMA5 algorithm is implemented in the PE for generic code
        /// authentication in AArch64 state.
        GPA OFFSET(24) NUMBITS(4) [
            NotSupported = 0b0000,
            Supported = 0b0001
        ],

        /// Indicates whether an IMPLEMENTATION DEFINED algorithm is implemented in the PE for
        /// address authentication, in AArch64 state. This applies to all Pointer Authentication
        /// instructions other than the PACGA instruction.
        API OFFSET(8) NUMBITS(4) [],

        /// Indicates whether the QARMA5 algorithm is implemented in the PE for address
        /// authentication, in AArch64 state. This applies to all Pointer Authentication
        /// instructions other than the PACGA instruction.
        APA OFFSET(4) NUMBITS(4) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ID_AA64ISAR1_EL1::Register;

    sys_coproc_read_raw!(u64, "ID_AA64ISAR1_EL1", "x");
}

pub const ID_AA64ISAR1_EL1: Reg = Reg {};
