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

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers/TTBR1-EL1--Translation-Table-Base-Register-1--EL1-
register_bitfields! {u64,
    pub TTBR1_EL1 [
        /// ASID, bits [55:48] An ASID for the translation table base address.
        /// The TTBCR.A1 field selects either TTBR0.ASID or TTBR1.ASID.
        ASID OFFSET(48) NUMBITS(8) [],

        /// Translation table base address
        BADDR OFFSET(1) NUMBITS(47) [],

        /// Common not Private.
        /// When TTBCR.EAE ==1, this bit indicates whether each entry that is pointed to by TTBR1 is a member of a common set
        /// that can be used by every PE in the Inner Shareable domain for which the value of TTBR1.CnP is 1.
        CNP OFFSET(0) NUMBITS(1) []
    ]
}

pub struct Ttbr1El1;

impl Readable for Ttbr1El1 {
    type T = u64;
    type R = TTBR1_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, ttbr1_el1",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for Ttbr1El1 {
    type T = u64;
    type R = TTBR1_EL1::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr ttbr1_el1, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const TTBR1_EL1: Ttbr1El1 = Ttbr1El1 {};
