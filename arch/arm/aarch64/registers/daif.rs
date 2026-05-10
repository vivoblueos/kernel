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

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers/DAIF--Interrupt-Mask-Bits
register_bitfields! {u64,
    /// DAIF (Interrupt Mask Bits) Register
    pub DAIF [
         /// Debug mask bit
        D OFFSET(9) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// SError interrupt mask bit
        A OFFSET(8) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// IRQ mask bit
        I OFFSET(7) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// FIQ mask bit
        F OFFSET(6) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ]
    ]
}

pub struct Daif;

impl Readable for Daif {
    type T = u64;
    type R = DAIF::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, daif",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for Daif {
    type T = u64;
    type R = DAIF::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr daif, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const DAIF: Daif = Daif {};
