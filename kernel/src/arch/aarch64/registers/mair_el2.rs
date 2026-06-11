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

register_bitfields! {u64,
    pub MAIR_EL2 [
        /// Attribute 1 - Normal Memory Outer
        Attr1_Normal_Outer OFFSET(12) NUMBITS(4) [
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        /// Attribute 1 - Normal Memory Inner
        Attr1_Normal_Inner OFFSET(8) NUMBITS(4) [
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        /// Attribute 0 - Device Memory
        Attr0_Device OFFSET(0) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck    = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck       = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck          = 0b0000_1100
        ]
    ]
}

pub struct MairEl2;

impl Readable for MairEl2 {
    type T = u64;
    type R = MAIR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, mair_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for MairEl2 {
    type T = u64;
    type R = MAIR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr mair_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const MAIR_EL2: MairEl2 = MairEl2 {};
