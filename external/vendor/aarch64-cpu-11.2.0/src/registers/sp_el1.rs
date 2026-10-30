// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! The stack pointer - EL1
//!
//! Holds the stack pointer associated with EL1. When executing at EL1, the value of SPSel.SP
//! determines the current stack pointer:
//!
//! SPSel.SP | current stack pointer
//! --------------------------------
//! 0        | SP_EL0
//! 1        | SP_EL1

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "SP_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "SP_EL1", "x");
}

pub const SP_EL1: Reg = Reg {};
