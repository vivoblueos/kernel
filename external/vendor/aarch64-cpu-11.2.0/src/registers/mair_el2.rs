// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Erik Verbruggen <erik.verbruggen@me.com>
//   - Bradley Landherr <landhb@users.noreply.github.com>

//! Memory Attribute Indirection Register - EL2
//!
//! Provides the memory attribute encodings corresponding to the possible AttrIndx values in a
//! Long-descriptor format translation table entry for stage 1 translations at EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub MAIR_EL2 [
        /// Attribute 7
        Attr7_Normal_Outer OFFSET(60) NUMBITS(4) [
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr7_Normal_Inner OFFSET(56) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr6_Normal_Inner OFFSET(48) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr5_Normal_Inner OFFSET(40) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr4_Normal_Inner OFFSET(32) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr3_Normal_Inner OFFSET(24) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr2_Normal_Inner OFFSET(16) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr1_Normal_Inner OFFSET(8) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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
            Device = 0b0000,

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
            nonGathering_nonReordering_noEarlyWriteAck = 0b0000_0000,
            nonGathering_nonReordering_EarlyWriteAck = 0b0000_0100,
            nonGathering_Reordering_EarlyWriteAck = 0b0000_1000,
            Gathering_Reordering_EarlyWriteAck = 0b0000_1100
        ],
        Attr0_Normal_Inner OFFSET(0) NUMBITS(4) [
            WriteThrough_Transient = 0x0000,
            WriteThrough_Transient_WriteAlloc = 0x0001,
            WriteThrough_Transient_ReadAlloc = 0x0010,
            WriteThrough_Transient_ReadWriteAlloc = 0x0011,

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

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = MAIR_EL2::Register;

    sys_coproc_read_raw!(u64, "MAIR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = MAIR_EL2::Register;

    sys_coproc_write_raw!(u64, "MAIR_EL2", "x");
}

pub const MAIR_EL2: Reg = Reg {};
