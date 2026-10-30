// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Interrupt Controller Control Register - EL1
//!
//! Controls aspects of the behavior of the GIC CPU interface and provides information
//! about the features implemented.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub ICC_CTLR_EL1 [
        /// Extended INTID range (read-only).
        ExtRange OFFSET(19) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ICC_CTLR_EL1::Register;

    sys_coproc_read_raw!(u64, "ICC_CTLR_EL1", "x");
}

pub const ICC_CTLR_EL1: Reg = Reg {};
