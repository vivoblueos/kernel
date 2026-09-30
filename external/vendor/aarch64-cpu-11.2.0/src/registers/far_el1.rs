// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Fault Address Register - EL1
//!
//! Holds the faulting Virtual Address for all synchronous Instruction or Data Abort, PC alignment
//! fault and Watchpoint exceptions that are taken to EL1.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "FAR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "FAR_EL1", "x");
}

pub const FAR_EL1: Reg = Reg {};
