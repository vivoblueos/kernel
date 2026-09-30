// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Bradley Landherr <landhb@users.noreply.github.com>

//! Translation Control Register - EL2
//!
//! The control register for stage 1 of the EL2, or EL2&0 translation regime.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub TCR_EL2 [

        /// When FEAT_HAFDBS is implemented hardware can update the dirty flags in the stage1
        /// descriptors
        HD OFFSET(22) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HAFDBS is implemented hardware can update the access flags in the stage1
        /// descriptors
        HA OFFSET(21) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// Top Byte ignored - indicates whether the top byte of an address is used for address
        /// match for the TTBR0_EL2 region, or ignored and used for tagged addresses. Defined values
        /// are:
        ///
        /// 0 Top Byte used in the address calculation.
        ///
        /// 1 Top Byte ignored in the address calculation.
        ///
        /// This affects addresses generated in EL2 using AArch64 where the address would be
        /// translated by tables pointed to by TTBR0_EL2. It has an effect whether the EL2,
        /// or EL2&0, translation regime is enabled or not.
        ///
        /// If ARMv8.3-PAuth is implemented and TCR_EL2.TBID1 is 1, then this field only applies to
        /// Data accesses.
        ///
        /// If the value of TBI is 1, then bits[63:56] of that target address are also set to 0
        /// before the address is stored in the PC, in the following cases:
        ///
        /// • A branch or procedure return within EL2.
        /// • An exception taken to EL2.
        /// • An exception return to EL2.
        TBI OFFSET(20) NUMBITS(1) [
            Used = 0,
            Ignored = 1
        ],

        /// Physical Address Size.
        ///
        /// 000 32 bits, 4GiB.
        /// 001 36 bits, 64GiB.
        /// 010 40 bits, 1TiB.
        /// 011 42 bits, 4TiB.
        /// 100 44 bits, 16TiB.
        /// 101 48 bits, 256TiB.
        /// 110 52 bits, 4PB
        ///
        /// Other values are reserved.
        ///
        /// The reserved values behave in the same way as the 101 or 110 encoding, but software must
        /// not rely on this property as the behavior of the reserved values might change in a
        /// future revision of the architecture.
        ///
        /// The value 110 is permitted only if ARMv8.2-LPA is implemented and the translation
        /// granule size is 64KiB.
        ///
        /// In an implementation that supports 52-bit PAs, if the value of this field is not 110 ,
        /// then bits[51:48] of every translation table base address for the stage of translation
        /// controlled by TCR_EL2 are 0000.
        PS OFFSET(16) NUMBITS(3) [
            Bits_32 = 0b000,
            Bits_36 = 0b001,
            Bits_40 = 0b010,
            Bits_42 = 0b011,
            Bits_44 = 0b100,
            Bits_48 = 0b101,
            Bits_52 = 0b110
        ],

        /// Granule size for the TTBR0_EL2.
        ///
        /// 0b00 4KiB
        /// 0b01 64KiB
        /// 0b10 16KiB
        ///
        /// Other values are reserved.
        ///
        /// If the value is programmed to either a reserved value, or a size that has not been
        /// implemented, then the hardware will treat the field as if it has been programmed to an
        /// IMPLEMENTATION DEFINED choice of the sizes that has been implemented for all purposes
        /// other than the value read back from this register.
        ///
        /// It is IMPLEMENTATION DEFINED whether the value read back is the value programmed or the
        /// value that corresponds to the size chosen.
        TG0 OFFSET(14) NUMBITS(2) [
            KiB_4 = 0b00,
            KiB_64 = 0b01,
            KiB_16 = 0b10
        ],

        /// Shareability attribute for memory associated with translation table walks using
        /// TTBR0_EL2.
        ///
        /// 00 Non-shareable
        /// 01 Reserved
        /// 10 Outer Shareable
        /// 11 Inner Shareable
        ///
        /// Other values are reserved.
        SH0 OFFSET(12) NUMBITS(2) [
            None = 0b00,
            Outer = 0b10,
            Inner = 0b11
        ],

        /// Outer cacheability attribute for memory associated with translation table walks using
        /// TTBR0_EL2.
        ///
        /// 00 Normal memory, Outer Non-cacheable
        ///
        /// 01 Normal memory, Outer Write-Back Read-Allocate Write-Allocate Cacheable
        ///
        /// 10 Normal memory, Outer Write-Through Read-Allocate No Write-Allocate Cacheable
        ///
        /// 11 Normal memory, Outer Write-Back Read-Allocate No Write-Allocate Cacheable
        ORGN0 OFFSET(10) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],

        /// Inner cacheability attribute for memory associated with translation table walks using
        /// TTBR0_EL2.
        ///
        /// 00 Normal memory, Inner Non-cacheable
        ///
        /// 01 Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable
        ///
        /// 10 Normal memory, Inner Write-Through Read-Allocate No Write-Allocate Cacheable
        ///
        /// 11 Normal memory, Inner Write-Back Read-Allocate No Write-Allocate Cacheable
        IRGN0 OFFSET(8) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],


        /// The size offset of the memory region addressed by TTBR0_EL2. The region size is
        /// 2^(64-T0SZ) bytes.
        ///
        /// The maximum and minimum possible values for T0SZ depend on the level of translation
        /// table and the memory translation granule size, as described in the AArch64 Virtual
        /// Memory System Architecture chapter.
        T0SZ OFFSET(0) NUMBITS(6) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = TCR_EL2::Register;

    sys_coproc_read_raw!(u64, "TCR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = TCR_EL2::Register;

    sys_coproc_write_raw!(u64, "TCR_EL2", "x");
}

pub const TCR_EL2: Reg = Reg {};
