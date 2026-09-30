// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2022 Amazon.com, Inc. or its affiliates.
// Author(s):
//   - Javi Merino <javmer@amazon.com>

//! Software Thread ID Register - EL2.
//!
//! Provides a location where software executing at EL2 can store thread identifying information,
//! for OS management purposes.

use tock_registers::interfaces::{Readable, Writeable};

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "TPIDR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "TPIDR_EL2", "x");
}

pub const TPIDR_EL2: Reg = Reg {};
