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

// See: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/VTCR-EL2--Virtualization-Translation-Control-Register
register_bitfields! {u64,
    pub VTCR_EL2 [
        /// Physical address size for second stage translation
        PS OFFSET(16) NUMBITS(3) [
            PA_32B_4GB   = 0b000,
            PA_36B_64GB  = 0b001,
            PA_40B_1TB   = 0b010,
            PA_42B_4TB   = 0b011,
            PA_44B_16TB  = 0b100,
            PA_48B_256TB = 0b101
        ],

        /// Granule size for stage 2 translation
        TG0 OFFSET(14) NUMBITS(2) [
            Granule4KB  = 0b00,
            Granule64KB = 0b01,
            Granule16KB = 0b10
        ],

        /// Outer cacheability for stage 2 translation table walks
        ORGN0 OFFSET(10) NUMBITS(2) [
            NonCacheable  = 0b00,
            NormalWBRAWA  = 0b01,
            NormalWT      = 0b10,
            NormalWBnWA   = 0b11
        ],

        /// Inner cacheability for stage 2 translation table walks
        IRGN0 OFFSET(8) NUMBITS(2) [
            NonCacheable  = 0b00,
            NormalWBRAWA  = 0b01,
            NormalWT      = 0b10,
            NormalWBnWA   = 0b11
        ],

        /// Shareability for stage 2 translation table walks
        SH0 OFFSET(12) NUMBITS(2) [
            NonShareable   = 0b00,
            OuterShareable = 0b10,
            Inner          = 0b11
        ],

        /// Starting level of the stage 2 translation lookup
        SL0 OFFSET(6) NUMBITS(2) [],

        /// The size offset of the memory region for stage 2 (region size = 2^(64-T0SZ))
        T0SZ OFFSET(0) NUMBITS(6) []
    ]
}

pub struct VtcrEl2;

impl Readable for VtcrEl2 {
    type T = u64;
    type R = VTCR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, vtcr_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for VtcrEl2 {
    type T = u64;
    type R = VTCR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr vtcr_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const VTCR_EL2: VtcrEl2 = VtcrEl2 {};