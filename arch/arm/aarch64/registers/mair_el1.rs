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

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers/MAIR-EL1--Memory-Attribute-Indirection-Register--EL1-
register_bitfields! {u64,
    pub MAIR_EL1 [
        /// Attribute 7
        Attr7_Normal_Outer OFFSET(60) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr7_Device OFFSET(56) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr7_Normal_Inner OFFSET(56) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 6
        Attr6_Normal_Outer OFFSET(52) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr6_Device OFFSET(48) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr6_Normal_Inner OFFSET(48) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 5
        Attr5_Normal_Outer OFFSET(44) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr5_Device OFFSET(40) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr5_Normal_Inner OFFSET(40) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 4
        Attr4_Normal_Outer OFFSET(36) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr4_Device OFFSET(32) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr4_Normal_Inner OFFSET(32) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 3
        Attr3_Normal_Outer OFFSET(28) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr3_Device OFFSET(24) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr3_Normal_Inner OFFSET(24) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 2
        Attr2_Normal_Outer OFFSET(20) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr2_Device OFFSET(16) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr2_Normal_Inner OFFSET(16) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 1
        Attr1_Normal_Outer OFFSET(12) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr1_Device OFFSET(8) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr1_Normal_Inner OFFSET(8) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],

        /// Attribute 0
        Attr0_Normal_Outer OFFSET(4) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ],
        Attr0_Device OFFSET(0) NUMBITS(8) [
            NonGathering_NonReordering_NonEarlyWriteAck = 0b0000_0000,
            NonGathering_NonReordering_EarlyWriteAck = 0b0000_0100,
            NonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr0_Normal_Inner OFFSET(0) NUMBITS(4) [
            WriteThrough_Transient_WriteAlloc = 0b0001,
            WriteThrough_Transient_ReadAlloc = 0b0010,
            WriteThrough_Transient_ReadWriteAlloc = 0b0011,

            NonCacheable = 0b0100,
            WriteBack_Transient_WriteAlloc = 0b0101,
            WriteBack_Transient_ReadAlloc = 0b0110,
            WriteBack_Transient_ReadWriteAlloc = 0b0111,

            WriteThrough_NonTransient = 0b1000,
            WriteThrough_NonTransient_WriteAlloc = 0b1001,
            WriteThrough_NonTransient_ReadAlloc = 0b1010,
            WriteThrough_NonTransient_ReadWriteAlloc = 0b1011,

            WriteBack_NonTransient = 0b1100,
            WriteBack_NonTransient_WriteAlloc = 0b1101,
            WriteBack_NonTransient_ReadAlloc = 0b1110,
            WriteBack_NonTransient_ReadWriteAlloc = 0b1111
        ]
    ]
}

pub struct MairEl1;

impl Readable for MairEl1 {
    type T = u64;
    type R = MAIR_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, mair_el1",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for MairEl1 {
    type T = u64;
    type R = MAIR_EL1::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr mair_el1, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const MAIR_EL1: MairEl1 = MairEl1 {};
