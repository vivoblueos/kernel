// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2020-2023 by the author(s)
//
// Author(s):
//   - Chris Brown <ccbrown112@gmail.com>

//! Debug Data Transfer Register, half-duplex
//!
//! Transfers 64 bits of data between the PE and an external debugger. Can transfer both ways using
//! only a single register.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub DBGDTR_EL0 [
        /// Writes to this register set DTRRX to the value in this field and do not change RXfull.
        ///
        /// Reads of this register:
        ///
        ///   - If RXfull is set to 1, return the last value written to DTRTX.
        ///   - If RXfull is set to 0, return an UNKNOWN value.
        ///
        /// After the read, RXfull is cleared to 0.
        HighWord OFFSET(32) NUMBITS(32) [],

        /// Writes to this register set DTRTX to the value in this field and set TXfull to 1.
        ///
        /// Reads of this register:
        ///
        ///   - If RXfull is set to 1, return the last value written to DTRRX.
        ///   - If RXfull is set to 0, return an UNKNOWN value.
        ///
        /// After the read, RXfull is cleared to 0.
        LowWord OFFSET(0) NUMBITS(32) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = DBGDTR_EL0::Register;

    sys_coproc_read_raw!(u64, "DBGDTR_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = DBGDTR_EL0::Register;

    sys_coproc_write_raw!(u64, "DBGDTR_EL0", "x");
}

pub const DBGDTR_EL0: Reg = Reg {};
