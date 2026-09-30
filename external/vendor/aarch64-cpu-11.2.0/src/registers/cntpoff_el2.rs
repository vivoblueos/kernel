// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Counter-timer Physical Offset register - EL2
//!
//! Holds the 64-bit physical offset.
//! This is the offset for the AArch64 physical timers and counters
//! when Enhanced Counter Virtualization is enabled.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "CNTPOFF_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "CNTPOFF_EL2", "x");
}

pub const CNTPOFF_EL2: Reg = Reg {};
