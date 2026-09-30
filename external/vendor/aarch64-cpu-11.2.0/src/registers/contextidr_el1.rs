// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Yan Tan <tanyan@kylinos.cn>

//! Context ID Register
//!
//! Holds the Process Context ID (PCID) for the current process.
//! This register is used to identify the current process context.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CONTEXTIDR_EL1 [
        // Reserved, RES0，[63:32]

        /// Process Identifier
        ///
        /// This field must be programmed with a unique value that identifies the current process.
        ///
        /// - In AArch32 state, when TTBCR.EAE is set to 0, CONTEXTIDR.ASID holds the ASID
        /// - In AArch64 state, CONTEXTIDR_EL1 is independent of the ASID, \
        ///   and for the EL1&0 translation regime either TTBR0_EL1 or TTBR1_EL1 holds the ASID.
        ///
        /// On a Cold reset, this field resets to an architecturally UNKNOWN value
        PROCID OFFSET(0) NUMBITS(32) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CONTEXTIDR_EL1::Register;

    sys_coproc_read_raw!(u64, "S3_0_C13_C0_1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CONTEXTIDR_EL1::Register;

    sys_coproc_write_raw!(u64, "S3_0_C13_C0_1", "x");
}

pub const CONTEXTIDR_EL1: Reg = Reg {};
