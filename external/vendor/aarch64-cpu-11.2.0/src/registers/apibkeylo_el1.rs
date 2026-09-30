// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2023 Amazon.com, Inc. or its affiliates.
//
// Author(s):
//   - Ugur Usug <ugurus@amazon.com>

//! Pointer Authentication Key B for Instruction Low - EL1
//!
//! Holds bits[63:0] of key B used for authentication of instruction pointer values.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "APIBKeyLo_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "APIBKeyLo_EL1", "x");
}

pub const APIBKEYLO_EL1: Reg = Reg {};
