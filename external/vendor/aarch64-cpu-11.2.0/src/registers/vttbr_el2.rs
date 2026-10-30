// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - KarimAllah Ahmed <karahmed@amazon.com>
//   - Andre Richter <andre.o.richter@gmail.com>

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub VTTBR_EL2 [
        /// An VMID for the translation table
        ///
        /// If the implementation only supports 8-bit VM IDs the top 8 bits are RES0
        VMID  OFFSET(48) NUMBITS(16) [],

        /// Translation table base address
        BADDR OFFSET(1) NUMBITS(47) [],

        /// Common not Private
        CnP   OFFSET(0) NUMBITS(1) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = VTTBR_EL2::Register;

    sys_coproc_read_raw!(u64, "VTTBR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = VTTBR_EL2::Register;

    sys_coproc_write_raw!(u64, "VTTBR_EL2", "x");
}

impl Reg {
    #[inline(always)]
    pub fn get_baddr(&self) -> u64 {
        self.read(VTTBR_EL2::BADDR) << 1
    }

    #[inline(always)]
    pub fn set_baddr(&self, addr: u64) {
        self.write(VTTBR_EL2::BADDR.val(addr >> 1));
    }
}

pub const VTTBR_EL2: Reg = Reg {};
