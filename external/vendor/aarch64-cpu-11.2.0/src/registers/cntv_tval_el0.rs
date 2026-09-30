// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Gregor Reitzenstein <me@dequbed.space>

//! Counter-timer Virtual Timer TimerValue register - EL0
//!
//! Holds the timer value for the EL1 virtual timer.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "CNTV_TVAL_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "CNTV_TVAL_EL0", "x");
}

pub const CNTV_TVAL_EL0: Reg = Reg {};
