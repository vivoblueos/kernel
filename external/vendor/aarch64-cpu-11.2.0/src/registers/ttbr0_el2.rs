// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Bradley Landherr <landhb@users.noreply.github.com>

//! Translation Table Base Register 0 - EL2
//!
//! Holds the base address of the translation table for the initial lookup for stage 1 of the
//! translation of an address from the lower VA range for accesses from EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub TTBR0_EL2 [
        /// Reserved
        RES0  OFFSET(48) NUMBITS(16) [],

        /// Translation table base address
        BADDR OFFSET(1) NUMBITS(48) [],

        /// Common not Private
        CnP   OFFSET(0) NUMBITS(1) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = TTBR0_EL2::Register;

    sys_coproc_read_raw!(u64, "TTBR0_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = TTBR0_EL2::Register;

    sys_coproc_write_raw!(u64, "TTBR0_EL2", "x");
}

impl Reg {
    #[inline(always)]
    pub fn get_baddr(&self) -> u64 {
        self.read(TTBR0_EL2::BADDR) << 1
    }

    #[inline(always)]
    pub fn set_baddr(&self, addr: u64) {
        self.write(TTBR0_EL2::BADDR.val(addr >> 1));
    }
}

pub const TTBR0_EL2: Reg = Reg {};
