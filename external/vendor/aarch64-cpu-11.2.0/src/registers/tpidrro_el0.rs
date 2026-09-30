// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2020-2023 by the author(s)
//
// Author(s):
//   - Erik Verbruggen <erikjv@me.com>

//! Read-Only Software Thread ID Register - EL0.
//!
//! Provides a location where software executing at EL1 or higher can store thread identifying
//! information that is visible to software executing at EL0, for OS management purposes.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "TPIDRRO_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "TPIDRRO_EL0", "x");
}

pub const TPIDRRO_EL0: Reg = Reg {};
