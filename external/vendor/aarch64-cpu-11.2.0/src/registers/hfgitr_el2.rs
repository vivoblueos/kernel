// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HFGITR-EL2--Hypervisor-Fine-Grained-Instruction-Trap-Register?lang=en

//! Hypervisor Fine-Grained Instruction Trap Register - EL2
//!
//! Provides instruction trap controls for EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HFGITR_EL2 [
        /// [63] Trap execution of PSBCSYNC at EL1 to EL2
        PSBCSYNC     OFFSET(63) NUMBITS(1) [],
        /// [62] Trap execution of AT S1E1A at EL1 using AArch64 to EL2
        ATS1E1A      OFFSET(62) NUMBITS(1) [],
        // 61: Reserved (RES0)
        /// [60] Trap execution of COSP-related context instructions at EL1 to EL2
        COSPRCTX     OFFSET(60) NUMBITS(1) [],
        /// [59] Trap execution of GCSEPP at EL1 to EL2
        nGCSEPP      OFFSET(59) NUMBITS(1) [],
        /// [58] Trap execution of GCSSTR_EL1 at EL1 to EL2
        nGCSSTR_EL1  OFFSET(58) NUMBITS(1) [],
        /// [57] Trap execution of GCSPUSHM_EL1 at EL1 to EL2
        nGCSPUSHM_EL1 OFFSET(57) NUMBITS(1) [],
        /// [56] Trap execution of BRBIALL at EL1 to EL2
        nBRBIALL     OFFSET(56) NUMBITS(1) [],
        /// [55] Trap execution of BRBINJ at EL1 to EL2
        nBRBINJ      OFFSET(55) NUMBITS(1) [],
        /// [54] Trap execution of DCCVAC at EL1 to EL2
        DCCVAC       OFFSET(54) NUMBITS(1) [],
        /// [53] Trap execution of SVC at EL1 to EL2
        SVC_EL1      OFFSET(53) NUMBITS(1) [],
        /// [52] Trap execution of SVC at EL0 to EL2
        SVC_EL0      OFFSET(52) NUMBITS(1) [],
        /// [51] Trap execution of ERET at EL1 to EL2
        ERET         OFFSET(51) NUMBITS(1) [],
        /// [50] Trap execution of CPPRCTX at EL1 to EL2
        CPPRCTX      OFFSET(50) NUMBITS(1) [],
        /// [49] Trap execution of DVPRCTX at EL1 to EL2
        DVPRCTX      OFFSET(49) NUMBITS(1) [],
        /// [48] Trap execution of CFPRCTX at EL1 to EL2
        CFPRCTX      OFFSET(48) NUMBITS(1) [],
        /// [47] Trap execution of TLBIVAALE1 at EL1 to EL2
        TLBIVAALE1   OFFSET(47) NUMBITS(1) [],
        /// [46] Trap execution of TLBIVALE1 at EL1 to EL2
        TLBIVALE1    OFFSET(46) NUMBITS(1) [],
        /// [45] Trap execution of TLBIVAAE1 at EL1 to EL2
        TLBIVAAE1    OFFSET(45) NUMBITS(1) [],
        /// [44] Trap execution of TLBIASIDE1 at EL1 to EL2
        TLBIASIDE1   OFFSET(44) NUMBITS(1) [],
        /// [43] Trap execution of TLBIVAE1 at EL1 to EL2
        TLBIVAE1     OFFSET(43) NUMBITS(1) [],
        /// [42] Trap execution of TLBIVMALLE1 at EL1 to EL2
        TLBIVMALLE1  OFFSET(42) NUMBITS(1) [],
        /// [41] Trap execution of TLBIRVAALE1 at EL1 to EL2
        TLBIRVAALE1  OFFSET(41) NUMBITS(1) [],
        /// [40] Trap execution of TLBIRVALE1 at EL1 to EL2
        TLBIRVALE1   OFFSET(40) NUMBITS(1) [],
        /// [39] Trap execution of TLBIRVAAE1 at EL1 to EL2
        TLBIRVAAE1   OFFSET(39) NUMBITS(1) [],
        /// [38] Trap execution of TLBIRVAE1 at EL1 to EL2
        TLBIRVAE1    OFFSET(38) NUMBITS(1) [],
        /// [37] Trap execution of TLBIRVAALE1IS at EL1 to EL2
        TLBIRVAALE1IS OFFSET(37) NUMBITS(1) [],
        /// [36] Trap execution of TLBIRVALE1IS at EL1 to EL2
        TLBIRVALE1IS OFFSET(36) NUMBITS(1) [],
        /// [35] Trap execution of TLBIRVAAE1IS at EL1 to EL2
        TLBIRVAAE1IS OFFSET(35) NUMBITS(1) [],
        /// [34] Trap execution of TLBIRVAE1IS at EL1 to EL2
        TLBIRVAE1IS  OFFSET(34) NUMBITS(1) [],
        /// [33] Trap execution of TLBIVAALE1IS at EL1 to EL2
        TLBIVAALE1IS OFFSET(33) NUMBITS(1) [],
        /// [32] Trap execution of TLBIVALE1IS at EL1 to EL2
        TLBIVALE1IS  OFFSET(32) NUMBITS(1) [],
        /// [31] Trap execution of TLBIVAAE1IS at EL1 to EL2
        TLBIVAAE1IS  OFFSET(31) NUMBITS(1) [],
        /// [30] Trap execution of TLBIASIDE1IS at EL1 to EL2
        TLBIASIDE1IS OFFSET(30) NUMBITS(1) [],
        /// [29] Trap execution of TLBIVAE1IS at EL1 to EL2
        TLBIVAE1IS   OFFSET(29) NUMBITS(1) [],
        /// [28] Trap execution of TLBIVMALLE1IS at EL1 to EL2
        TLBIVMALLE1IS OFFSET(28) NUMBITS(1) [],
        /// [27] Trap execution of TLBIRVAALE1OS at EL1 to EL2
        TLBIRVAALE1OS OFFSET(27) NUMBITS(1) [],
        /// [26] Trap execution of TLBIRVALE1OS at EL1 to EL2
        TLBIRVALE1OS OFFSET(26) NUMBITS(1) [],
        /// [25] Trap execution of TLBIRVAAE1OS at EL1 to EL2
        TLBIRVAAE1OS OFFSET(25) NUMBITS(1) [],
        /// [24] Trap execution of TLBIRVAE1OS at EL1 to EL2
        TLBIRVAE1OS  OFFSET(24) NUMBITS(1) [],
        /// [23] Trap execution of TLBIVAALE1OS at EL1 to EL2
        TLBIVAALE1OS OFFSET(23) NUMBITS(1) [],
        /// [22] Trap execution of TLBIVALE1OS at EL1 to EL2
        TLBIVALE1OS  OFFSET(22) NUMBITS(1) [],
        /// [21] Trap execution of TLBIVAAE1OS at EL1 to EL2
        TLBIVAAE1OS  OFFSET(21) NUMBITS(1) [],
        /// [20] Trap execution of TLBIASIDE1OS at EL1 to EL2
        TLBIASIDE1OS OFFSET(20) NUMBITS(1) [],
        /// [19] Trap execution of TLBIVAE1OS at EL1 to EL2
        TLBIVAE1OS   OFFSET(19) NUMBITS(1) [],
        /// [18] Trap execution of TLBIVMALLE1OS at EL1 to EL2
        TLBIVMALLE1OS OFFSET(18) NUMBITS(1) [],
        /// [17] Trap execution of ATS1E1WP at EL1 to EL2
        ATS1E1WP     OFFSET(17) NUMBITS(1) [],
        /// [16] Trap execution of ATS1E1RP at EL1 to EL2
        ATS1E1RP     OFFSET(16) NUMBITS(1) [],
        /// [15] Trap execution of ATS1E0W at EL1 to EL2
        ATS1E0W      OFFSET(15) NUMBITS(1) [],
        /// [14] Trap execution of ATS1E0R at EL1 to EL2
        ATS1E0R      OFFSET(14) NUMBITS(1) [],
        /// [13] Trap execution of ATS1E1W at EL1 to EL2
        ATS1E1W      OFFSET(13) NUMBITS(1) [],
        /// [12] Trap execution of ATS1E1R at EL1 to EL2
        ATS1E1R      OFFSET(12) NUMBITS(1) [],
        /// [11] Trap execution of DCZVA at EL1 to EL2
        DCZVA        OFFSET(11) NUMBITS(1) [],
        /// [10] Trap execution of DCCIVAC at EL1 to EL2
        DCCIVAC      OFFSET(10) NUMBITS(1) [],
        /// [9] Trap execution of DCCVADP at EL1 to EL2
        DCCVADP      OFFSET(9) NUMBITS(1) [],
        /// [8] Trap execution of DCCVAP at EL1 to EL2
        DCCVAP       OFFSET(8) NUMBITS(1) [],
        /// [7] Trap execution of DCCVAU at EL1 to EL2
        DCCVAU       OFFSET(7) NUMBITS(1) [],
        /// [6] Trap execution of DCCISW at EL1 to EL2
        DCCISW       OFFSET(6) NUMBITS(1) [],
        /// [5] Trap execution of DCCSW at EL1 to EL2
        DCCSW        OFFSET(5) NUMBITS(1) [],
        /// [4] Trap execution of DCISW at EL1 to EL2
        DCISW        OFFSET(4) NUMBITS(1) [],
        /// [3] Trap execution of DCIVAC at EL1 to EL2
        DCIVAC       OFFSET(3) NUMBITS(1) [],
        /// [2] Trap execution of IC IVAU at EL1/EL0 to EL2
        ICIVAU       OFFSET(2) NUMBITS(1) [],
        /// [1] Trap execution of IC IALLU at EL1 to EL2
        ICIALLU      OFFSET(1) NUMBITS(1) [],
        /// [0] Trap execution of IC IALLUIS at EL1 to EL2
        ICIALLUIS    OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HFGITR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C1_C1_6", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HFGITR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C1_C1_6", "x");
}

pub const HFGITR_EL2: Reg = Reg {};
