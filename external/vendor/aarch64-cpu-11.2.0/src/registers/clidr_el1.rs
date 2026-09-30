// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Valentin B. <valentin.be@protonmail.com>

//! Cache Level ID Register - EL1
//!
//! Identifies the type of cache, or caches, that are implemented at each level and can
//! be managed using the architected cache maintenance instructions that operate by set/way,
//! up to a maximum of seven levels. Also identifies the Level of Coherence (LoC) and Level
//! of Unification (LoU) for the cache hierarchy.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CLIDR_EL1 [
        /// Tag cache type 7.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype7 OFFSET(45) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 6.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype6 OFFSET(43) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 5.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype5 OFFSET(41) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 4.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype4 OFFSET(39) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 3.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype3 OFFSET(37) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 2.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype2 OFFSET(35) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Tag cache type 1.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Indicates the type of cache that is implemented and can be
        /// managed using the architected cache maintenance instructions that operate
        /// by set/way at each level, from Level 1 up to a maximum of seven levels of
        /// cache hierarchy.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        Ttype1 OFFSET(33) NUMBITS(2) [
            /// No Tag Cache.
            NoTag = 0b00,
            /// Separate Allocation Tag Cache.
            SeparateAllocationTag = 0b01,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in unified lines.
            UnifiedAllocationTagDataCombined = 0b10,
            /// Unified Allocation Tag and Data cache, Allocation Tags and Data in separate lines.
            UnifiedAllocationTagDataSeparated = 0b11
        ],

        /// Inner cache boundary. This field indicates the boundary for caching
        /// Inner Cacheable memory regions.
        ICB OFFSET(30) NUMBITS(3) [
            /// Not disclosed by this mechanism.
            Undisclosed = 0b000,
            /// L1 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL1 = 0b001,
            /// L2 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL2 = 0b010,
            /// L3 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL3 = 0b011,
            /// L4 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL4 = 0b100,
            /// L5 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL5 = 0b101,
            /// L6 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL6 = 0b110,
            /// L7 cache is the highest Inner Cacheable level.
            HighestInnerCacheableL7 = 0b111
        ],

        /// Level of Unification Uniprocessor for the cache hierarchy.
        ///
        /// When FEAT_S2FWB is implemented, the architecture requires that this field
        /// is zero so that no levels of data cache need to be cleaned in order to
        /// manage coherency with instruction fetches.
        LoUU OFFSET(27) NUMBITS(3) [],

        /// Levels of Coherence for the cache hierarchy.
        LoC OFFSET(24) NUMBITS(3) [],

        /// Level of Unification Inner Shareable for the cache hierarchy.
        ///
        /// When FEAT_S2FWB is implemented, the architecture requires that this field
        /// is zero so that no levels of data cache need to be cleaned in order to
        /// manage coherency with instruction fetches.
        LoUIS OFFSET(21) NUMBITS(3) [],

        /// Cache Type field 7.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype7 OFFSET(18) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 6.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype6 OFFSET(15) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 5.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype5 OFFSET(12) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 4.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype4 OFFSET(9) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 3.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype3 OFFSET(6) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 2.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype2 OFFSET(3) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ],

        /// Cache Type field 1.
        ///
        /// Indicates the type of cache that is implemented and can be managed using
        /// the architected cache maintenance instructions that operate by set/way at
        /// each level, from Level 1 up to a maximum of seven levels of cache hierarchy.
        ///
        /// All values other than the defined ones are considered reserved.
        ///
        /// If software reads the Cache Type fields from [`CLIDR_EL1::Ctype1`] upwards,
        /// once it has seen a value of `000`, no caches that can be managed using the
        /// architected cache maintenance instructions that operate by set/way exist at
        /// further-out levels of the hierarchy. So, for example, if Ctype3 is the first
        /// Cache Type field with a value of `000`, the values of `Ctype4` to `Ctype7`
        /// must be ignored.
        Ctype1 OFFSET(0) NUMBITS(3) [
            /// No cache.
            NoCache = 0b000,
            /// Instruction cache only.
            InstructionCacheOnly = 0b001,
            /// Data cache only.
            DataCacheOnly = 0b010,
            /// Separate instruction and data caches.
            SeparateInstructionAndDataCaches = 0b011,
            /// Unified cache.
            UnifiedCache = 0b100
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CLIDR_EL1::Register;

    sys_coproc_read_raw!(u64, "CLIDR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CLIDR_EL1::Register;

    sys_coproc_write_raw!(u64, "CLIDR_EL1", "x");
}

pub const CLIDR_EL1: Reg = Reg;
