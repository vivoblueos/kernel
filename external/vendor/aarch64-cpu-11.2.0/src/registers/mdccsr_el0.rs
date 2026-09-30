// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2020-2023 by the author(s)
//
// Author(s):
//   - Chris Brown <ccbrown112@gmail.com>

//! Monitor DCC Status Register
//!
//! Transfers data from an external debugger to the PE. For example, it is used by a debugger
//! transferring commands and data to a debug target. See DBGDTR_EL0 for additional architectural
//! mappings. It is a component of the Debug Communications Channel.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub MDCCSR_EL0 [
        /// DTRRX full. Read-only view of the equivalent bit in the EDSCR.
        RXfull OFFSET(30) NUMBITS(1) [
            NotFull = 0,
            Full = 1
        ],

        /// DTRTX full. Read-only view of the equivalent bit in the EDSCR.
        TXfull OFFSET(29) NUMBITS(1) [
            NotFull = 0,
            Full = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = MDCCSR_EL0::Register;

    sys_coproc_read_raw!(u64, "MDCCSR_EL0", "x");
}

pub const MDCCSR_EL0: Reg = Reg {};
