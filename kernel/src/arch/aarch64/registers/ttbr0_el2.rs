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

// See: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/TTBR0-EL2--Translation-Table-Base-Register-0--EL2-
register_bitfields! {u64,
    pub TTBR0_EL2 [
        /// Translation table base address
        BADDR OFFSET(1) NUMBITS(47) [],

        /// Common not Private
        CNP OFFSET(0) NUMBITS(1) []
    ]
}

pub struct Ttbr0El2;

impl Readable for Ttbr0El2 {
    type T = u64;
    type R = TTBR0_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, ttbr0_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for Ttbr0El2 {
    type T = u64;
    type R = TTBR0_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr ttbr0_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const TTBR0_EL2: Ttbr0El2 = Ttbr0El2 {};
