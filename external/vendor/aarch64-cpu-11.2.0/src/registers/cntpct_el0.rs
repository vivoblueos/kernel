// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Counter-timer Physical Count register - EL0
//!
//! Holds the 64-bit physical count value.

use tock_registers::interfaces::Readable;

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "CNTPCT_EL0", "x");
}

pub const CNTPCT_EL0: Reg = Reg {};
