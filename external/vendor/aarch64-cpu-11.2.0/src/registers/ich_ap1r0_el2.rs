// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Interrupt Controller Hyp Active Priorities Group 1 Registers - EL2
//!
//! Provides information about Group 1 virtual active priorities for EL2.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "ICH_AP1R0_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "ICH_AP1R0_EL2", "x");
}

pub const ICH_AP1R0_EL2: Reg = Reg {};
