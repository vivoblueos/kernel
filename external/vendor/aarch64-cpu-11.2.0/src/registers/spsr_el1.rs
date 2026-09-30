// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Saved Program Status Register - EL1
//!
//! Holds the saved process state when an exception is taken to EL1.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub SPSR_EL1 [
        /// Negative condition flag.
        ///
        /// Set to the value of the N condition flag on taking an exception to EL1, and copied to
        /// the N condition flag on executing an exception return operation in EL1.
        ///
        /// Set to 1 if the result of the last flag-setting instruction was negative.
        N OFFSET(31) NUMBITS(1) [],

        /// Zero condition flag.
        ///
        /// Set to the value of the Z condition flag on taking an exception to EL1, and copied to
        /// the Z condition flag on executing an exception return operation in EL1.
        ///
        /// Set to 1 if the result of the last flag-setting instruction was zero, and to 0
        /// otherwise. A result of zero often indicates an equal result from a comparison.
        Z OFFSET(30) NUMBITS(1) [],

        /// Carry condition flag.
        ///
        /// Set to the value of the C condition flag on taking an exception to EL1, and copied to
        /// the C condition flag on executing an exception return operation in EL1.
        ///
        /// Set to 1 if the last flag-setting instruction resulted in a carry condition, for example
        /// an unsigned overflow on an addition.
        C OFFSET(29) NUMBITS(1) [],

        /// Overflow condition flag.
        ///
        /// Set to the value of the V condition flag on taking an exception to EL1, and copied to
        /// the V condition flag on executing an exception return operation in EL1.
        ///
        /// Set to 1 if the last flag-setting instruction resulted in an overflow condition, for
        /// example a signed overflow on an addition.
        V OFFSET(28) NUMBITS(1) [],

        /// Software step. Shows the value of PSTATE.SS immediately before the exception was taken.
        SS OFFSET(21) NUMBITS(1) [],

        /// Illegal Execution state bit. Shows the value of PSTATE.IL immediately before the
        /// exception was taken.
        IL OFFSET(20) NUMBITS(1) [],

        /// Process state D mask. The possible values of this bit are:
        ///
        /// 0 Watchpoint, Breakpoint, and Software Step exceptions targeted at the current Exception
        ///   level are not masked.
        ///
        /// 1 Watchpoint, Breakpoint, and Software Step exceptions targeted at the current Exception
        ///   level are masked.
        ///
        /// When the target Exception level of the debug exception is higher than the current
        /// Exception level, the exception is not masked by this bit.
        D OFFSET(9) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// SError interrupt mask bit. The possible values of this bit are:
        ///
        /// 0 Exception not masked.
        /// 1 Exception masked.
        A OFFSET(8) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// IRQ mask bit. The possible values of this bit are:
        ///
        /// 0 Exception not masked.
        /// 1 Exception masked.
        I OFFSET(7) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// FIQ mask bit. The possible values of this bit are:
        ///
        /// 0 Exception not masked.
        /// 1 Exception masked.
        F OFFSET(6) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// AArch64 state (Exception level and selected SP) that an exception was taken from. The
        /// possible values are:
        ///
        /// M[3:0] | State
        /// --------------
        /// 0b0000 | EL0t
        /// 0b0100 | EL1t
        /// 0b0101 | EL1h
        ///
        /// Other values are reserved, and returning to an Exception level that is using AArch64
        /// with a reserved value in this field is treated as an illegal exception return.
        ///
        /// The bits in this field are interpreted as follows:
        ///   - M[3:2] holds the Exception Level.
        ///   - M[1] is unused and is RES 0 for all non-reserved values.
        ///   - M[0] is used to select the SP:
        ///     - 0 means the SP is always SP0.
        ///     - 1 means the exception SP is determined by the EL.
        M OFFSET(0) NUMBITS(4) [
            EL0t = 0b0000,
            EL1t = 0b0100,
            EL1h = 0b0101
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = SPSR_EL1::Register;

    sys_coproc_read_raw!(u64, "SPSR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = SPSR_EL1::Register;

    sys_coproc_write_raw!(u64, "SPSR_EL1", "x");
}

pub const SPSR_EL1: Reg = Reg {};
