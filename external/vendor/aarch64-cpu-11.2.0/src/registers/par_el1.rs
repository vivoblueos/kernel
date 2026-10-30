// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2021-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Physical Address Register - EL1
//!
//! Returns the output address (OA) from an Address translation instruction that executed
//! successfully, or fault information if the instruction did not execute successfully.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub PAR_EL1 [
        /// Output address. The output address (OA) corresponding to the supplied input address.
        /// This field returns address bits[47:12].
        ///
        /// When ARMv8.2-LPA is implemented, and 52-bit addresses and a 64KB translation granule are
        /// in use, the PA[51:48] bits form the upper part of the address value. Otherwise the
        /// PA[51:48] bits are RES0.
        ///
        /// For implementations with fewer than 48 physical address bits, the corresponding upper
        /// bits in this field are RES0.
        ///
        /// This field resets to an architecturally UNKNOWN value.
        PA OFFSET(12) NUMBITS(36) [],

        /// Indicates whether the instruction performed a successful address translation.
        ///
        /// 0 Address translation completed successfully.
        ///
        /// 1 Address translation aborted.
        ///
        /// This field resets to an architecturally UNKNOWN value.
        F OFFSET(0) NUMBITS(1) [
            TranslationSuccessfull = 0,
            TranslationAborted = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = PAR_EL1::Register;

    sys_coproc_read_raw!(u64, "PAR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = PAR_EL1::Register;

    sys_coproc_write_raw!(u64, "PAR_EL1", "x");
}

pub const PAR_EL1: Reg = Reg {};
