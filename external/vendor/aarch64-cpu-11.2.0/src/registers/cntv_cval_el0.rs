// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Javier Alvarez <javier.alvarez@allthingsembedded.net>

//! Counter-timer Virtual Timer CompareValue register - EL0
//!
//! Holds the compare value for the virtual timer.
//!
//! When CNTV_CTL_EL0.ENABLE is 1, the timer condition is met when (CNTVCT_EL0 - CompareValue) is
//! greater than or equal to zero. This means that CompareValue acts like a 64-bit upcounter timer.
//!
//! When the timer condition is met:
//!   - CNTV_CTL_EL0.ISTATUS is set to 1.
//!   - If CNTV_CTL_EL0.IMASK is 0, an interrupt is generated.
//!
//! When CNTV_CTL_EL0.ENABLE is 0, the timer condition is not met, but CNTVCT_EL0 continues to
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

    sys_coproc_read_raw!(u64, "CNTV_CVAL_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "CNTV_CVAL_EL0", "x");
}

pub const CNTV_CVAL_EL0: Reg = Reg {};
