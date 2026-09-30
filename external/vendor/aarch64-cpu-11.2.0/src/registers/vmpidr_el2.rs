// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Callum Thomson <callumthom11@gmail.com>

//! Virtual Multiprocessor ID Register - EL2
//!
//! Holds the value returned for EL1 reads of MPIDR_EL1.

use tock_registers::interfaces::Writeable;
use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub VMPIDR_EL2 [
        /// Affinity level 3. See the description of Aff0 for more information.
        Aff3 OFFSET(32) NUMBITS(8) [],

        /// Reserved, RES1.
        RES1 OFFSET(31) NUMBITS(1) [],

        /// Indicates a Uniprocessor system, as distinct from PE 0 in a multiprocessor system.
        U OFFSET(30) NUMBITS(1) [
            MultiprocessorSystem = 0b0,
            UniprocessorSystem = 0b1,
        ],

        /// Indicates whether the lowest level of affinity consists of logical PEs that are implemented using a
        /// multithreading type approach. See the description of Aff0 for more information about affinity levels
        MT OFFSET(24) NUMBITS(1) [],

        /// Affinity level 2. See the description of Aff0 for more information.
        Aff2 OFFSET(16) NUMBITS(8) [],

        /// Affinity level 1. See the description of Aff0 for more information.
        Aff1 OFFSET(8) NUMBITS(8) [],

        /// Affinity level 0.  This is the affinity level that is most significant for determining PE behavior.  Higher
        /// affinity levels are increasingly less significant in determining PE behavior.
        Aff0 OFFSET(0) NUMBITS(8) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = VMPIDR_EL2::Register;

    sys_coproc_read_raw!(u64, "VMPIDR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = VMPIDR_EL2::Register;

    sys_coproc_write_raw!(u64, "VMPIDR_EL2", "x");
}

pub const VMPIDR_EL2: Reg = Reg {};
