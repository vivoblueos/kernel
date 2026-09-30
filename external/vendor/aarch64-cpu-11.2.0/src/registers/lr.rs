// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Alban Seurat <alban.seurat@me.com>

//! The link register

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    read_raw!(u64, "lr", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    write_raw!(u64, "lr", "x");
}

pub const LR: Reg = Reg {};
