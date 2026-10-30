// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Yan Tan <tanyan@kylinos.cn>

//! Auxiliary Fault Status Register 0 - EL1
//!
//! Provides IMPLEMENTATION DEFINED fault status information for synchronous aborts that are taken to EL1.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "S3_0_C5_C1_0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "S3_0_C5_C1_0", "x");
}

pub const AFSR0_EL1: Reg = Reg {};
