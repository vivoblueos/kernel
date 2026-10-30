// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HAFGRTR-EL2--Hypervisor-Activity-Monitors-Fine-Grained-Read-Trap-Register?lang=en

//! Hypervisor Activity Monitors Fine-Grained Read Trap Register - EL2
//!
//! Provides controls for traps of MRS reads of Activity Monitors System registers.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HAFGRTR_EL2 [
        // 63-50: RES0, Reserved bits, write 0
        /// Trap MRS reads of AMEVTYPER115_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER115_EL0 OFFSET(49) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR115_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR115_EL0  OFFSET(48) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER114_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER114_EL0 OFFSET(47) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR114_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR114_EL0  OFFSET(46) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER113_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER113_EL0 OFFSET(45) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR113_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR113_EL0  OFFSET(44) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER112_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER112_EL0 OFFSET(43) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR112_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR112_EL0  OFFSET(42) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER111_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER111_EL0 OFFSET(41) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR111_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR111_EL0  OFFSET(40) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER110_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER110_EL0 OFFSET(39) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR110_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR110_EL0  OFFSET(38) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER19_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER19_EL0  OFFSET(37) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR19_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR19_EL0   OFFSET(36) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER18_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER18_EL0  OFFSET(35) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR18_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR18_EL0   OFFSET(34) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER17_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER17_EL0  OFFSET(33) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR17_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR17_EL0   OFFSET(32) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER16_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER16_EL0  OFFSET(31) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR16_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR16_EL0   OFFSET(30) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER15_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER15_EL0  OFFSET(29) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR15_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR15_EL0   OFFSET(28) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER14_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER14_EL0  OFFSET(27) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR14_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR14_EL0   OFFSET(26) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER13_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER13_EL0  OFFSET(25) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR13_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR13_EL0   OFFSET(24) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER12_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER12_EL0  OFFSET(23) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR12_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR12_EL0   OFFSET(22) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER11_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER11_EL0  OFFSET(21) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR11_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR11_EL0   OFFSET(20) NUMBITS(1) [],
        /// Trap MRS reads of AMEVTYPER10_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVTYPER10_EL0  OFFSET(19) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR10_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR10_EL0   OFFSET(18) NUMBITS(1) [],
        /// Trap MRS reads of AMCNTEN1 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMCNTEN1        OFFSET(17) NUMBITS(1) [],
        // 16-5: RES0, Reserved bits, write 0
        /// Trap MRS reads of AMEVCNTR03_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR03_EL0  OFFSET(4) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR02_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR02_EL0  OFFSET(3) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR01_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR01_EL0  OFFSET(2) NUMBITS(1) [],
        /// Trap MRS reads of AMEVCNTR00_EL0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMEVCNTR00_EL0  OFFSET(1) NUMBITS(1) [],
        /// Trap MRS reads of AMCNTEN0 at EL1/EL0 using AArch64 or MRC at EL0 using AArch32 to EL2.
        AMCNTEN0        OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HAFGRTR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C3_C1_6", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HAFGRTR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C3_C1_6", "x");
}

pub const HAFGRTR_EL2: Reg = Reg {};
