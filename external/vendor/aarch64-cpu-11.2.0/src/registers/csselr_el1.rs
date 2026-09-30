// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Valentin B. <valentin.be@protonmail.com>

//! Cache Size Selection Register - EL1
//!
//! Selects the current Cache Size ID Register, CCSIDR_EL1, by specifying the
//! required cache level and the cache type (either instruction or data cache).

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CSSELR_EL1 [
        /// Allocation Tag not Data bit.
        ///
        /// **When `FEAT_MTE2` is implemented:**
        ///
        /// When [`CSSELR_EL1::InD`] is set, this bit is considered reserved.
        ///
        /// When [`CSSELR_EL1::Level`] is programmed to a cache level that is
        /// not implemented, this field's value will be undefined for reads.
        ///
        /// NOTE: On a Warm reset, this field resets to an architecturally
        /// undefined value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        TnD OFFSET(4) NUMBITS(1) [
            /// Data, Instruction or Unified cache.
            Data = 0b0,
            /// Separate Allocation Tag cache.
            AllocationTag = 0b1
        ],

        /// Cache level of required cache.
        ///
        /// Any value other than the pre-defined ones are considered reserved
        /// and shall not be written to this field.
        ///
        /// When [`CSSELR_EL1::Level`] is programmed to a cache level that is
        /// not implemented, this field's value will be undefined for reads.
        ///
        /// NOTE: On a Warm reset, this field resets to an architecturally
        /// undefined value.
        Level OFFSET(1) NUMBITS(3) [
            /// Level 1 Cache.
            L1 = 0b000,
            /// Level 2 Cache.
            L2 = 0b001,
            /// Level 3 Cache.
            L3 = 0b010,
            /// Level 4 Cache.
            L4 = 0b011,
            /// Level 5 Cache.
            L5 = 0b100,
            /// Level 6 Cache.
            L6 = 0b101,
            /// Level 7 Cache.
            L7 = 0b110
        ],

        /// Instruction not Data bit.
        ///
        /// When [`CSSELR_EL1::Level`] is programmed to a cache level that is
        /// not implemented, this field's value will be undefined for reads.
        ///
        /// NOTE: On a Warm reset, this field resets to an architecturally
        /// undefined value.
        InD OFFSET(0) NUMBITS(1) [
            /// Data or Unified cache.
            Data = 0b0,
            /// Instruction cache.
            Instruction = 0b1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CSSELR_EL1::Register;

    sys_coproc_read_raw!(u64, "CSSELR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CSSELR_EL1::Register;

    sys_coproc_write_raw!(u64, "CSSELR_EL1", "x");
}

pub const CSSELR_EL1: Reg = Reg;
