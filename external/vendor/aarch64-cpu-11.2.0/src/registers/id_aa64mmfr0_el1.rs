// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! AArch64 Memory Model Feature Register 0 - EL1
//!
//! Provides information about the implemented memory model and memory
//! management support in AArch64 state.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub ID_AA64MMFR0_EL1 [
        /// Support for 4KiB memory translation granule size. Defined values are:
        ///
        /// 0000 4KiB granule supported.
        /// 1111 4KiB granule not supported.
        ///
        /// All other values are reserved.
        TGran4  OFFSET(28) NUMBITS(4) [
            Supported = 0b0000,
            NotSupported = 0b1111
        ],

        /// Support for 64KiB memory translation granule size. Defined values are:
        ///
        /// 0000 64KiB granule supported.
        /// 1111 64KiB granule not supported.
        ///
        /// All other values are reserved.
        TGran64 OFFSET(24) NUMBITS(4) [
            Supported = 0b0000,
            NotSupported = 0b1111
        ],

        /// Support for 16KiB memory translation granule size. Defined values are:
        ///
        /// 0001 16KiB granule supported.
        /// 0000 16KiB granule not supported.
        ///
        /// All other values are reserved.
        TGran16 OFFSET(20) NUMBITS(4) [
            Supported = 0b0001,
            NotSupported = 0b0000
        ],

        /// Number of bits supported in the ASID:
        ///
        /// 0000 ASIDs are 8 bits.
        /// 0010 ASIDs are 16 bits.
        ///
        /// All other values are reserved.
        ASIDBits OFFSET(4) NUMBITS(4) [
            Bits_8 = 0b0000,
            Bits_16 = 0b0010
        ],

        /// Physical Address range supported. Defined values are:
        ///
        /// 0000 32 bits, 4GiB.
        /// 0001 36 bits, 64GiB.
        /// 0010 40 bits, 1TiB.
        /// 0011 42 bits, 4TiB.
        /// 0100 44 bits, 16TiB.
        /// 0101 48 bits, 256TiB.
        /// 0110 52 bits, 4PiB.
        ///
        /// All other values are reserved.
        ///
        /// The value 0110 is permitted only if the implementation includes ARMv8.2-LPA, otherwise
        /// it is reserved.
        PARange OFFSET(0) NUMBITS(4) [
            Bits_32 = 0b0000,
            Bits_36 = 0b0001,
            Bits_40 = 0b0010,
            Bits_42 = 0b0011,
            Bits_44 = 0b0100,
            Bits_48 = 0b0101,
            Bits_52 = 0b0110
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ID_AA64MMFR0_EL1::Register;

    sys_coproc_read_raw!(u64, "ID_AA64MMFR0_EL1", "x");
}

pub const ID_AA64MMFR0_EL1: Reg = Reg {};
