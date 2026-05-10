// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use tock_registers::{interfaces::*, register_bitfields};

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers/TCR-EL1--Translation-Control-Register--EL1-
register_bitfields! {u64,
    pub TCR_EL1 [
        /// When FEAT_MTE_NO_ADDRESS_TAGS is implemented or FEAT_MTE_CANONICAL_TAGS is implemented:
        /// Extended memory tag checking.
        /// This field controls address generation and tag checking when EL0 and EL1 are using AArch64
        /// where the data address would be translated by tables pointed to by TTBR1_EL1.
        /// This control has an effect regardless of whether stage 1 of the EL1&0 translation regime is enabled or not.
        MTX1 OFFSET(61) NUMBITS(1) [],

        /// When FEAT_MTE_NO_ADDRESS_TAGS is implemented or FEAT_MTE_CANONICAL_TAGS is implemented:
        /// Extended memory tag checking.
        /// This field controls address generation and tag checking when EL0 and EL1 are using AArch64
        /// where the data address would be translated by tables pointed to by TTBR0_EL1.
        /// This control has an effect regardless of whether stage 1 of the EL1&0 translation regime is enabled or not.
        MTX0 OFFSET(60) NUMBITS(1) [],

        /// When FEAT_LPA2 is implemented and (FEAT_D128 is not implemented or TCR2_EL1.D128 == 0):
        /// This field affects:
        /// 1.Whether a 52-bit output address can be described by the translation tables of the 4KB or 16KB
        /// translation granules.
        /// 2. The minimum value of TCR_EL1.{T0SZ,T1SZ}.
        /// 3.How and where shareability for Block and Page descriptors are encoded.
        DS OFFSET(59) NUMBITS(1) [],

        /// When FEAT_MTE2 is implemented:
        /// Controls the generation of Unchecked accesses at EL1,
        /// and at EL0 if the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// when address[59:55] = 0b11111.
        TCMA1 OFFSET(58) NUMBITS(1) [],

        /// When FEAT_MTE2 is implemented:
        /// Controls the generation of Unchecked accesses at EL1,
        /// and at EL0 if the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// when address[59:55] = 0b00000.
        TCMA0 OFFSET(57) NUMBITS(1) [],

        /// When FEAT_E0PD is implemented:
        /// Faulting control for unprivileged access to any address translated by TTBR1_EL1.
        E0PD1 OFFSET(56) NUMBITS(1) [
            NotGenerateFault  = 0,
            Level0TranslationFault = 1,
        ],

        /// When FEAT_E0PD is implemented:
        /// Faulting control for unprivileged access to any address translated by TTBR0_EL1.
        E0PD0 OFFSET(55) NUMBITS(1) [
            NotGenerateFault  = 0,
            Level0TranslationFault = 1,
        ],

        /// When FEAT_SVE is implemented or FEAT_TME is implemented:
        /// Non-Fault translation timing Disable when using TTBR1_EL1.
        /// Controls how a TLB miss is reported in response to a non-fault unprivileged access for
        /// a virtual address that is translated using TTBR1_EL1.
        NFD1 OFFSET(54) NUMBITS(1) [
            NonAffectTLB = 0,
            AffectTLB = 1,
        ],

        /// When FEAT_SVE is implemented or FEAT_TME is implemented:
        /// Non-Fault translation timing Disable when using TTBR0_EL1.
        /// Controls how a TLB miss is reported in response to a non-fault unprivileged access for
        /// a virtual address that is translated using TTBR0_EL1.
        NFD0 OFFSET(53) NUMBITS(1) [
            NonAffectTLB = 0,
            AffectTLB = 1,
        ],

        /// When FEAT_PAuth is implemented:
        /// Controls the use of the top byte of instruction addresses for address matching.
        /// This affects addresses where the address would be translated by tables pointed to by TTBR1_EL1.
        TBID1 OFFSET(52) NUMBITS(1) [
            InstructionAndData = 0,
            DataOnly = 1,
        ],

        /// When FEAT_PAuth is implemented:
        /// Controls the use of the top byte of instruction addresses for address matching.
        /// This affects addresses where the address would be translated by tables pointed to by TTBR0_EL1.
        TBID0 OFFSET(51) NUMBITS(1) [
            InstructionAndData = 0,
            DataOnly = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[62]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR1_EL1.
        HWU0162 OFFSET(50) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[61]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR1_EL1.
        HWU0161 OFFSET(49) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[60]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR1_EL1.
        HWU0160 OFFSET(48) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[59]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR1_EL1.
        HWU0159 OFFSET(47) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[62]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR0_EL1.
        HWU062 OFFSET(46) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[61]
        /// of the stage 1 translation table Block or Page entry for translations using TTBR0_EL1.
        HWU061 OFFSET(45) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[60] of
        /// the stage 1 translation table Block or Page entry for translations using TTBR0_EL1.
        HWU060 OFFSET(44) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],


        /// When FEAT_HPDS2 is implemented:
        /// Hardware Use. Indicates IMPLEMENTATION DEFINED hardware use of bit[59] of
        /// the stage 1 translation table Block or Page entry for translations using TTBR0_EL1.
        HWU059 OFFSET(43) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS is implemented:
        /// Hierarchical Permission Disables. This affects the hierarchical control bits,
        /// APTable, PXNTable, and UXNTable, except NSTable, in the translation tables pointed to by TTBR1_EL1.
        HPD1 OFFSET(42) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HPDS is implemented:
        /// Hierarchical Permission Disables. This affects the hierarchical control bits,
        /// APTable, PXNTable, and UXNTable, except NSTable, in the translation tables pointed to by TTBR0_EL1.
        HPD0 OFFSET(41) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HAFDBS is implemented:
        /// Hardware management of dirty state in stage 1 translations from EL0 and EL1.
        HD OFFSET(40) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_HAFDBS is implemented:
        /// Hardware Access flag update in stage 1 translations from EL0 and EL1.
        HA OFFSET(39) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// Top Byte ignored. Indicates whether the top byte of an address is used for
        /// address match for the TTBR1_EL1 region, or ignored and used for tagged addresses.
        TBI1 OFFSET(38) NUMBITS(1) [
            Used = 0,
            Ignored = 1
        ],

        /// Top Byte ignored. Indicates whether the top byte of an address is used for
        /// address match for the TTBR0_EL1 region, or ignored and used for tagged addresses.
        TBI0 OFFSET(37) NUMBITS(1) [
            Used = 0,
            Ignored = 1
        ],

        /// ASID Size. Defined values are:
        AS OFFSET(36) NUMBITS(1) [
            Bits_8 = 0,
            Bits_16 = 1
        ],

        /// Intermediate Physical Address Size.
        ///
        /// 000 32 bits, 4GiB.
        /// 001 36 bits, 64GiB.
        /// 010 40 bits, 1TiB.
        /// 011 42 bits, 4TiB.
        /// 100 44 bits, 16TiB.
        /// 101 48 bits, 256TiB.
        /// 110 52 bits, 4PiB
        IPS OFFSET(32) NUMBITS(3) [
            Bits_32 = 0b000,
            Bits_36 = 0b001,
            Bits_40 = 0b010,
            Bits_42 = 0b011,
            Bits_44 = 0b100,
            Bits_48 = 0b101,
            Bits_52 = 0b110
        ],

        /// Granule size for the TTBR1_EL1.
        TG1 OFFSET(30) NUMBITS(2) [
            KiB_4 = 0b10,
            KiB_16 = 0b01,
            KiB_64 = 0b11
        ],

        /// Shareability attribute for memory associated with translation table walks using TTBR1_EL1.
        SH1 OFFSET(28) NUMBITS(2) [
            NoneShareable = 0b00,
            OuterShareable = 0b10,
            InnerShareable = 0b11
        ],

        /// Outer cacheability attribute for memory associated with translation table walks using TTBR1_EL1.
        ORGN1 OFFSET(26) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],

        /// Inner cacheability attribute for memory associated with translation table walks using TTBR1_EL1.
        IRGN1 OFFSET(24) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],

        /// Translation table walk disable for translations using TTBR1_EL1.
        /// This bit controls whether a translation table walk is performed on a TLB miss,
        /// for an address that is translated using TTBR1_EL1.
        EPD1 OFFSET(23) NUMBITS(1) [
            EnableTTBR1Walks = 0,
            DisableTTBR1Walks = 1
        ],

        /// Selects whether TTBR0_EL1 or TTBR1_EL1 defines the ASID.
        A1 OFFSET(22) NUMBITS(1) [
            TTBR0 = 0,
            TTBR1 = 1
        ],

        /// The size offset of the memory region addressed by TTBR1_EL1.
        /// The region size is 2(64-T1SZ) bytes.
        /// The maximum and minimum possible values for T1SZ depend on
        /// the level of translation table and the memory translation granule size,
        /// as described in the AArch64 Virtual Memory System Architecture chapter.
        T1SZ OFFSET(16) NUMBITS(6) [],

        /// Granule size for the TTBR0_EL1.
        TG0 OFFSET(14) NUMBITS(2) [
            KiB_4 = 0b00,
            KiB_16 = 0b10,
            KiB_64 = 0b01
        ],

        /// Shareability attribute for memory associated with translation table walks using TTBR0_EL1.
        SH0 OFFSET(12) NUMBITS(2) [
            NoneShareable = 0b00,
            OuterShareable = 0b10,
            InnerShareable = 0b11
        ],

        /// Outer cacheability attribute for memory associated with translation table walks using TTBR0_EL1.
        ORGN0 OFFSET(10) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],

        /// Inner cacheability attribute for memory associated with translation table walks using TTBR0_EL1.
        IRGN0 OFFSET(8) NUMBITS(2) [
            NonCacheable = 0b00,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b11
        ],

        /// Translation table walk disable for translations using TTBR0_EL1.
        /// This bit controls whether a translation table walk is performed on a TLB miss,
        /// for an address that is translated using TTBR0_EL1.
        EPD0 OFFSET(7) NUMBITS(1) [
            EnableTTBR0Walks = 0b0,
            DisableTTBR0Walks = 0b1
        ],

        /// The size offset of the memory region addressed by TTBR0_EL1.
        /// The region size is 2(64-T0SZ) bytes.
        /// The maximum and minimum possible values for T0SZ depend on
        /// the level of translation table and the memory translation granule size,
        /// as described in the AArch64 Virtual Memory System Architecture chapter.
        T0SZ OFFSET(0) NUMBITS(5) []
    ]
}

pub struct TcrEl1;

impl Readable for TcrEl1 {
    type T = u64;
    type R = TCR_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, tcr_el1",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for TcrEl1 {
    type T = u64;
    type R = TCR_EL1::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr tcr_el1, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const TCR_EL1: TcrEl1 = TcrEl1 {};
