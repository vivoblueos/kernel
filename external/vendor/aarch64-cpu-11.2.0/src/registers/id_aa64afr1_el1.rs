// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! AArch64 Auxiliary Feature Register 1 - EL1
//!
//! Reserved for future expansion of information about the IMPLEMENTATION DEFINED
//! features of the PE in AArch64 state.

use tock_registers::interfaces::Readable;

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "ID_AA64AFR1_EL1", "x");
}

pub const ID_AA64AFR1_EL1: Reg = Reg {};
