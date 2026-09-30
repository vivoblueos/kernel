// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Javier Alvarez <javier.alvarez@allthingsembedded.net>

//! Vector Base Address Register - EL3
//!
//! Holds the vector base address for any exception that is taken to EL3.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "VBAR_EL3", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "VBAR_EL3", "x");
}

pub const VBAR_EL3: Reg = Reg {};
