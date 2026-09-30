// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Berkus Decker <berkus+github@metta.systems>

//! Exception Link Register - EL3
//!
//! When taking an exception to EL3, holds the address to return to.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "ELR_EL3", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "ELR_EL3", "x");
}

pub const ELR_EL3: Reg = Reg {};
