// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

// See: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/TCR-EL2--Translation-Control-Register--EL2-
register_bitfields! {u64,
    pub TCR_EL2 [
        /// Physical address size
        PS OFFSET(16) NUMBITS(3) [
            Bits_32 = 0b000,
            Bits_36 = 0b001,
            Bits_40 = 0b010,
            Bits_42 = 0b011,
            Bits_44 = 0b100,
            Bits_48 = 0b101
        ],

        /// Granule size for TTBR0_EL2
        TG0 OFFSET(14) NUMBITS(2) [
            KiB_4  = 0b00,
            KiB_64 = 0b01,
            KiB_16 = 0b10
        ],

        /// Outer cacheability attribute for memory associated with translation table walks using TTBR0_EL2
        ORGN0 OFFSET(10) NUMBITS(2) [
            NonCacheable                            = 0b00,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b11
        ],

        /// Inner cacheability attribute for memory associated with translation table walks using TTBR0_EL2
        IRGN0 OFFSET(8) NUMBITS(2) [
            NonCacheable                            = 0b00,
            WriteBack_ReadAlloc_NoWriteAlloc_Cacheable = 0b01,
            WriteThrough_ReadAlloc_NoWriteAlloc_Cacheable = 0b10,
            WriteBack_ReadAlloc_WriteAlloc_Cacheable = 0b11
        ],

        /// Shareability attribute for memory associated with translation table walks using TTBR0_EL2
        SH0 OFFSET(12) NUMBITS(2) [
            NonShareable  = 0b00,
            OuterShareable = 0b10,
            Inner         = 0b11
        ],

        /// The size offset of the memory region addressed by TTBR0_EL2 (region size = 2^(64-T0SZ))
        T0SZ OFFSET(0) NUMBITS(6) []
    ]
}

pub struct TcrEl2;

impl Readable for TcrEl2 {
    type T = u64;
    type R = TCR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, tcr_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for TcrEl2 {
    type T = u64;
    type R = TCR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr tcr_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const TCR_EL2: TcrEl2 = TcrEl2 {};