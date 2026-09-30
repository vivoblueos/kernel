// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Counter-timer Physical Timer CompareValue register - EL0
//!
//! Holds the compare value for the EL1 physical timer.
//!
//! When CNTP_CTL_EL0.ENABLE is 1, the timer condition is met when (CNTPCT_EL0 - CompareValue) is
//! greater than or equal to zero. This means that CompareValue acts like a 64-bit upcounter timer.
//!
//! When the timer condition is met:
//!   - CNTP_CTL_EL0.ISTATUS is set to 1.
//!   - If CNTP_CTL_EL0.IMASK is 0, an interrupt is generated.
//!
//! When CNTP_CTL_EL0.ENABLE is 0, the timer condition is not met, but CNTPCT_EL0 continues to
//! count.
//!
//! If the Generic counter is implemented at a size less than 64 bits, then this field is permitted
//! to be implemented at the same width as the counter, and the upper bits are RES0.
//!
//! The value of this field is treated as zero-extended in all counter calculations.
//!
//! The reset behaviour of this field is:
//!   - On a Warm reset, this field resets to an architecturally UNKNOWN value.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "CNTP_CVAL_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "CNTP_CVAL_EL0", "x");
}

pub const CNTP_CVAL_EL0: Reg = Reg {};
