// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Yan Tan <tanyan@kylinos.cn>

//! Auxiliary Memory Attribute Indirection Register
//!
//! Provides IMPLEMENTATION DEFINED memory attributes for the stage 1 translation tables.
//! This register is used to define memory attributes that are not defined in the MAIR_EL1 register.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "S3_0_C10_C3_0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "S3_0_C10_C3_0", "x");
}

pub const AMAIR_EL1: Reg = Reg {};
