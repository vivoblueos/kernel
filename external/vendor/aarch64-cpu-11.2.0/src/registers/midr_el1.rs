// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Main ID Register - EL1
//!
//! Provides identification information for the processor, including an implementer code for the
//! device and a device ID number.

use tock_registers::{interfaces::Readable, register_bitfields};

register_bitfields! {u64,
    pub MIDR_EL1 [
        /// The Implementer code. This field must hold an implementer code that has been assigned by
        /// Arm. Assigned codes include the following:
        ///
        /// Hex representation Implementer
        /// 0x00               Reserved for software use
        /// 0xC0               Ampere Computing
        /// 0x41               Arm Limited
        /// 0x42               Broadcom Corporation
        /// 0x43               Cavium Inc.
        /// 0x44               Digital Equipment Corporation
        /// 0x46               Fujitsu Ltd.
        /// 0x49               Infineon Technologies AG
        /// 0x4D               Motorola or Freescale Semiconductor Inc.
        /// 0x4E               NVIDIA Corporation
        /// 0x50               Applied Micro Circuits Corporation
        /// 0x51               Qualcomm Inc.
        /// 0x56               Marvell International Ltd.
        /// 0x69               Intel Corporation
        ///
        /// Arm can assign codes that are not published in this manual. All values not assigned by
        /// Arm are reserved and must not be used.
        Implementer OFFSET(24) NUMBITS(8) [
            Reserved = 0x00,
            Ampere = 0xC0,
            Arm = 0x41,
            Broadcom = 0x42,
            Cavium = 0x43,
            DigitalEquipment = 0x44,
            Fujitsu = 0x46,
            Infineon = 0x49,
            MotorolaOrFreescale = 0x4D,
            NVIDIA = 0x4E,
            AppliedMicroCircuits = 0x50,
            Qualcomm = 0x51,
            Marvell = 0x56,
            Intel = 0x69
        ],

        /// An IMPLEMENTATION DEFINED variant number. Typically, this field is used to distinguish
        /// between different product variants, or major revisions of a product.
        Variant OFFSET(20) NUMBITS(4) [],

        /// The permitted values of this field are:
        ///
        /// 0001 Armv4.
        /// 0010 Armv4T.
        /// 0011 Armv5 (obsolete).
        /// 0100 Armv5T.
        /// 0101 Armv5TE.
        /// 0110 Armv5TEJ.
        /// 0111 Armv6.
        /// 1111 Architectural features are individually identified in the ID_* registers, see ID
        /// registers on page K14-8060.
        ///
        /// All other values are reserved.
        Architecture OFFSET(16) NUMBITS(4) [
            Individual = 0b1111
        ],

        /// An IMPLEMENTATION DEFINED primary part number for the device.
        ///
        /// On processors implemented by Arm, if the top four bits of the primary part number are
        /// 0x0 or 0x7, the variant and architecture are encoded differently.
        PartNum OFFSET(4) NUMBITS(12) [],

        /// An IMPLEMENTATION DEFINED revision number for the device.
        Revision OFFSET(0) NUMBITS(4) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = MIDR_EL1::Register;

    sys_coproc_read_raw!(u64, "MIDR_EL1", "x");
}

pub const MIDR_EL1: Reg = Reg {};
