// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! The stack pointer

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    read_raw!(u64, "sp", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    write_raw!(u64, "sp", "x");
}

pub const SP: Reg = Reg {};
