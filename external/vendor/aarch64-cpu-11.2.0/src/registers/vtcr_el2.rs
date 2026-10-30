// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Ali Saidi <alisaidi@amazon.com>

//! Virtualization Translation Control Register - EL2
//!
//! Provides control of stage2 translation of EL0/1

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub VTCR_EL2 [
        /// Reserved, RES1.
        RES1 OFFSET(31) NUMBITS(1) [],
        /// When FEAT_SEL2 is implemented:
        /// Non-secure stage 2 translation output address space for the Secure EL1&0 translation regime.
        NSA OFFSET(30) NUMBITS(1) [
            SecurePASpace = 0,
            NonSecurePASpace = 1,
        ],
        /// Hardware dirty flag update in stage2 translations when EL2 is enabled
        HD OFFSET(22) NUMBITS(1) [
            /// Stage2 hardware management of dirty state disabled
            Disabled = 0,
            /// Stage2 hardware management of dirty state enabled
            Enabled = 1,
        ],
        /// Hardware access flag update in stage2 translations when EL2 is enabled
        HA OFFSET(21) NUMBITS(1) [
            /// Stage2 hardware management of access state disabled
            Disabled = 0,
            /// Stage2 hardware management of access state enabled
            Enabled = 1,
        ],
        /// VMID Size
        VS OFFSET(19) NUMBITS(1) [
            /// 8-bit VMID
            Bits8 = 0,
            /// 16-bit VMID
            Bits16 = 1,
        ],
        /// Physical Address size of the second stage of translation
        PS OFFSET(16) NUMBITS(3) [
            /// 32 bits, 4GB
            PA_32B_4GB = 0b000,
            /// 36 bits, 64GB
            PA_36B_64GB = 0b001,
            /// 40 bits, 1TB
            PA_40B_1TB = 0b010,
            /// 42 bits, 4TB
            PA_42B_4TB = 0b011,
            /// 44 bits, 16TB
            PA_44B_16TB = 0b100,
            /// 48 bits, 256TB
            PA_48B_256TB = 0b101,
            /// 52 bits, 4PB
            PA_52B_4PB = 0b110,
        ],
        /// Granule size used for `VTTBR_EL2`
        TG0 OFFSET(14) NUMBITS(2) [
            /// Granule size of 4KB
            Granule4KB = 0b00,
            /// Granule size of 16KB
            Granule16KB = 0b10,
            /// Granule size of 64KB
            Granule64KB = 0b01,
        ],
        /// Shareability attribute for memory associated with translation table
        /// walks using `VTTBR_EL2` and `VSTTBR_EL2`
        SH0 OFFSET(12) NUMBITS(2) [
            /// Non-shareable
            Non = 0b00,
            /// Outer sharable
            Outer = 0b10,
            /// Inner sharable
            Inner = 0b11,
        ],
        /// Outer cacheability attribute for memory associated with translation table
        /// walks using `VTTBR_EL2` and `VSTTBR_EL2`
        ORGN0 OFFSET(10) NUMBITS(2) [
            /// Normal non-cacheable memory
            NormalNC = 0b00,
            /// Normal Write-back, Read-allocate, Write-allocate
            NormalWBRAWA = 0b01,
            /// Normal Write-through, Read-allocate, no Write-allocate
            NormalWTRAnWA = 0b10,
            /// Normal Write-back, Read-allocate, no Write-allocate
            NormalWBRAnWA = 0b11,
        ],
        /// Inner cacheability attribute for memory associated with translation table
        /// walks using `VTTBR_EL2` and `VSTTBR_EL2`
        IRGN0 OFFSET(8) NUMBITS(2) [
            /// Normal non-cacheable memory
            NormalNC = 0b00,
            /// Normal Write-back, Read-allocate, Write-allocate
            NormalWBRAWA = 0b01,
            /// Normal Write-through, Read-allocate, no Write-allocate
            NormalWTRAnWA = 0b10,
            /// Normal Write-back, Read-allocate, no Write-allocate
            NormalWBRAnWA = 0b11,
        ],
        /// Starting level of the stage2 translation lookup
        SL0 OFFSET(6) NUMBITS(2) [
            Granule4KBLevel2 = 0b00,
            Granule4KBLevel1 = 0b01,
            Granule4KBLevel0 = 0b10,
            Granule4KBLevel3 = 0b11,
        ],
        /// The size of the offest of the memory region addressed by the `VTTBR_EL2`
        T0SZ OFFSET(0) NUMBITS(6) [],

    ]
}
pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = VTCR_EL2::Register;

    sys_coproc_read_raw!(u64, "VTCR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = VTCR_EL2::Register;

    sys_coproc_write_raw!(u64, "VTCR_EL2", "x");
}

pub const VTCR_EL2: Reg = Reg {};
