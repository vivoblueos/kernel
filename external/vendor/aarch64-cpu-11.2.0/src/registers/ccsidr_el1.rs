// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Valentin B. <valentin.be@protonmail.com>

//! Current Cache Size ID Register - EL1
//!
//! Provides information about the architecture of the currently selected cache.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CCSIDR_EL1 [
        /// Number of sets in cache.
        ///
        /// A value of 0 indicates 1 set in the cache. The number does not
        /// necessarily have to be a power of 2.
        NumSetsWithCCIDX OFFSET(32) NUMBITS(24) [],

        /// Number of sets in cache.
        ///
        /// A value of 0 indicates 1 set in the cache. The number does not
        /// necessarily have to be a power of 2.
        NumSetsWithoutCCIDX OFFSET(13) NUMBITS(15) [],

        /// Associativity of cache.
        ///
        /// A value of 0 indicates an associativity of 1. The value does not
        /// necessarily have to be a power of 2.
        AssociativityWithCCIDX OFFSET(3) NUMBITS(21) [],

        /// Associativity of cache.
        ///
        /// A value of 0 indicates an associativity of 1. The value does not
        /// necessarily have to be a power of 2.
        AssociativityWithoutCCIDX OFFSET(3) NUMBITS(10) [],

        /// Log2(Number of bytes in cache lline) - 4.
        ///
        /// **Examples:**
        ///
        /// - For a line length of 16 bytes: Log2(16) - 4 = 0. This is the minimum line length.
        ///
        /// - For a line length of 32 bytes: Log2(32) - 4 = 1.
        LineSize OFFSET(0) NUMBITS(3) []
    ]
}

#[inline(always)]
fn has_feature_ccidx() -> bool {
    use crate::registers::ID_AA64MMFR2_EL1;

    ID_AA64MMFR2_EL1.read(ID_AA64MMFR2_EL1::CCIDX) != 0
}

pub struct Reg;

impl Reg {
    /// Reads the [`CCSIDR_EL1`] `NumSets` field, selecting the correct
    /// bit field by checking if the running CPU supports `CCIDX`.
    #[inline(always)]
    pub fn get_num_sets(&self) -> u64 {
        match has_feature_ccidx() {
            true => self.read(CCSIDR_EL1::NumSetsWithCCIDX),
            false => self.read(CCSIDR_EL1::NumSetsWithoutCCIDX),
        }
    }

    /// Sets the [`CCSIDR_EL1`] `NumSets` field, selecting the correct
    /// bit field by checking if the running CPU supports `CCIDX`.
    #[inline(always)]
    pub fn set_num_sets(&self, value: u64) {
        match has_feature_ccidx() {
            true => self.write(CCSIDR_EL1::NumSetsWithCCIDX.val(value)),
            false => self.write(CCSIDR_EL1::NumSetsWithoutCCIDX.val(value)),
        }
    }

    /// Reads the [`CCSIDR_EL1`] `Associativity` field, selecting the correct
    /// bit field by checking if the running CPU supports `CCIDX`.
    #[inline(always)]
    pub fn get_associativity(&self) -> u64 {
        match has_feature_ccidx() {
            true => self.read(CCSIDR_EL1::AssociativityWithCCIDX),
            false => self.read(CCSIDR_EL1::AssociativityWithoutCCIDX),
        }
    }

    /// Sets the [`CCSIDR_EL1`] `Associativity` field, selecting the correct
    /// bit field by checking if the running CPU supports `CCIDX`.
    #[inline(always)]
    pub fn set_associativity(&self, value: u64) {
        match has_feature_ccidx() {
            true => self.write(CCSIDR_EL1::AssociativityWithCCIDX.val(value)),
            false => self.write(CCSIDR_EL1::AssociativityWithoutCCIDX.val(value)),
        }
    }
}

impl Readable for Reg {
    type T = u64;
    type R = CCSIDR_EL1::Register;

    sys_coproc_read_raw!(u64, "CCSIDR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CCSIDR_EL1::Register;

    sys_coproc_write_raw!(u64, "CCSIDR_EL1", "x");
}

pub const CCSIDR_EL1: Reg = Reg;
