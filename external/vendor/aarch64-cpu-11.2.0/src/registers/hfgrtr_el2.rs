// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HFGRTR-EL2--Hypervisor-Fine-Grained-Read-Trap-Register?lang=en

//! Hypervisor Fine-Grained Read Trap Register - EL2
//!
//! Provides controls for traps of MRRS, MRS and MRC reads of System registers for EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HFGRTR_EL2 [
        /// Trap MRS reads of AMAIR2_EL1 at EL1 to EL2
        nAMAIR2_EL1   OFFSET(63) NUMBITS(1) [],
        /// Trap MRS reads of MAIR2_EL1 at EL1 to EL2
        nMAIR2_EL1    OFFSET(62) NUMBITS(1) [],
        /// Trap MRS reads of S2POR_EL1 at EL1 to EL2
        nS2POR_EL1    OFFSET(61) NUMBITS(1) [],
        /// Trap MRS reads of POR_EL1 at EL1 to EL2
        nPOR_EL1      OFFSET(60) NUMBITS(1) [],
        /// Trap MRS reads of POR_EL0 at EL1 to EL2
        nPOR_EL0      OFFSET(59) NUMBITS(1) [],
        /// Trap MRS reads of PIR_EL1 at EL1 to EL2
        nPIR_EL1      OFFSET(58) NUMBITS(1) [],
        /// Trap MRS reads of PIRE0_EL1 at EL1 to EL2
        nPIRE0_EL1    OFFSET(57) NUMBITS(1) [],
        /// Trap MRS reads of RCWMASK_EL1 at EL1 to EL2
        nRCWMASK_EL1  OFFSET(56) NUMBITS(1) [],
        /// Trap MRS reads of TPIDR2_EL0 at EL1 to EL2
        nTPIDR2_EL0   OFFSET(55) NUMBITS(1) [],
        /// Trap MRS reads of SMPRI_EL1 at EL1 to EL2
        nSMPRI_EL1    OFFSET(54) NUMBITS(1) [],
        /// Trap MRS reads of GCS_EL1 at EL1 to EL2
        nGCS_EL1      OFFSET(53) NUMBITS(1) [],
        /// Trap MRS reads of GCS_EL0 at EL1 to EL2
        nGCS_EL0      OFFSET(52) NUMBITS(1) [],
        // 51: RES0 (reserved)
        /// Trap MRS reads of ACCDATA_EL1 at EL1 to EL2
        nACCDATA_EL1  OFFSET(50) NUMBITS(1) [],
        /// Trap MRS reads of ERXADDR_EL1 at EL1 to EL2
        ERXADDR_EL1   OFFSET(49) NUMBITS(1) [],
        /// Trap MRS reads of ERXPFGCDN_EL1 at EL1 to EL2
        ERXPFGCDN_EL1 OFFSET(48) NUMBITS(1) [],
        /// Trap MRS reads of ERXPFGCTL_EL1 at EL1 to EL2
        ERXPFGCTL_EL1 OFFSET(47) NUMBITS(1) [],
        /// Trap MRS reads of ERXPFGF_EL1 at EL1 to EL2
        ERXPFGF_EL1   OFFSET(46) NUMBITS(1) [],
        /// Trap MRS reads of ERXMISCn_EL1 at EL1 to EL2
        ERXMISCn_EL1  OFFSET(45) NUMBITS(1) [],
        /// Trap MRS reads of ERXSTATUS_EL1 at EL1 to EL2
        ERXSTATUS_EL1 OFFSET(44) NUMBITS(1) [],
        /// Trap MRS reads of ERXCTLR_EL1 at EL1 to EL2
        ERXCTLR_EL1   OFFSET(43) NUMBITS(1) [],
        /// Trap MRS reads of ERXFR_EL1 at EL1 to EL2
        ERXFR_EL1     OFFSET(42) NUMBITS(1) [],
        /// Trap MRS reads of ERRSELR_EL1 at EL1 to EL2
        ERRSELR_EL1   OFFSET(41) NUMBITS(1) [],
        /// Trap MRS reads of ERRIDR_EL1 at EL1 to EL2
        ERRIDR_EL1    OFFSET(40) NUMBITS(1) [],
        /// Trap MRS reads of ICC_IGRPENn_EL1 at EL1 to EL2
        ICC_IGRPENn_EL1 OFFSET(39) NUMBITS(1) [],
        /// Trap MRS reads of VBAR_EL1 at EL1 to EL2
        VBAR_EL1      OFFSET(38) NUMBITS(1) [],
        /// Trap MRS reads of TTBR1_EL1 at EL1 to EL2
        TTBR1_EL1     OFFSET(37) NUMBITS(1) [],
        /// Trap MRS reads of TTBR0_EL1 at EL1 to EL2
        TTBR0_EL1     OFFSET(36) NUMBITS(1) [],
        /// Trap MRS reads of TPIDR_EL0 at EL1 to EL2
        TPIDR_EL0     OFFSET(35) NUMBITS(1) [],
        /// Trap MRS reads of TPIDRRO_EL0 at EL1 to EL2
        TPIDRRO_EL0   OFFSET(34) NUMBITS(1) [],
        /// Trap MRS reads of TPIDR_EL1 at EL1 to EL2
        TPIDR_EL1     OFFSET(33) NUMBITS(1) [],
        /// Trap MRS reads of TCR_EL1 at EL1 to EL2
        TCR_EL1       OFFSET(32) NUMBITS(1) [],
        /// Trap MRS reads of SCXTNUM_EL0 at EL1 to EL2
        SCXTNUM_EL0   OFFSET(31) NUMBITS(1) [],
        /// Trap MRS reads of SCXTNUM_EL1 at EL1 to EL2
        SCXTNUM_EL1   OFFSET(30) NUMBITS(1) [],
        /// Trap MRS reads of SCTLR_EL1 at EL1 to EL2
        SCTLR_EL1     OFFSET(29) NUMBITS(1) [],
        /// Trap MRS reads of REVIDR_EL1 at EL1 to EL2
        REVIDR_EL1    OFFSET(28) NUMBITS(1) [],
        /// Trap MRS reads of PAR_EL1 at EL1 to EL2
        PAR_EL1       OFFSET(27) NUMBITS(1) [],
        /// Trap MRS reads of MPIDR_EL1 at EL1 to EL2
        MPIDR_EL1     OFFSET(26) NUMBITS(1) [],
        /// Trap MRS reads of MIDR_EL1 at EL1 to EL2
        MIDR_EL1      OFFSET(25) NUMBITS(1) [],
        /// Trap MRS reads of MAIR_EL1 at EL1 to EL2
        MAIR_EL1      OFFSET(24) NUMBITS(1) [],
        /// Trap MRS reads of LORSA_EL1 at EL1 to EL2
        LORSA_EL1     OFFSET(23) NUMBITS(1) [],
        /// Trap MRS reads of LORN_EL1 at EL1 to EL2
        LORN_EL1      OFFSET(22) NUMBITS(1) [],
        /// Trap MRS reads of LORID_EL1 at EL1 to EL2
        LORID_EL1     OFFSET(21) NUMBITS(1) [],
        /// Trap MRS reads of LOREA_EL1 at EL1 to EL2
        LOREA_EL1     OFFSET(20) NUMBITS(1) [],
        /// Trap MRS reads of LORC_EL1 at EL1 to EL2
        LORC_EL1      OFFSET(19) NUMBITS(1) [],
        /// Trap MRS reads of ISR_EL1 at EL1 to EL2
        ISR_EL1       OFFSET(18) NUMBITS(1) [],
        /// Trap MRS reads of FAR_EL1 at EL1 to EL2
        FAR_EL1       OFFSET(17) NUMBITS(1) [],
        /// Trap MRS reads of ESR_EL1 at EL1 to EL2
        ESR_EL1       OFFSET(16) NUMBITS(1) [],
        /// Trap MRS reads of DCZID_EL0 at EL1 to EL2
        DCZID_EL0     OFFSET(15) NUMBITS(1) [],
        /// Trap MRS reads of CTR_EL0 at EL1 to EL2
        CTR_EL0       OFFSET(14) NUMBITS(1) [],
        /// Trap MRS reads of CSSELR_EL1 at EL1 to EL2
        CSSELR_EL1    OFFSET(13) NUMBITS(1) [],
        /// Trap MRS reads of CPACR_EL1 at EL1 to EL2
        CPACR_EL1     OFFSET(12) NUMBITS(1) [],
        /// Trap MRS reads of CONTEXTIDR_EL1 at EL1 to EL2
        CONTEXTIDR_EL1 OFFSET(11) NUMBITS(1) [],
        /// Trap MRS reads of CLIDR_EL1 at EL1 to EL2
        CLIDR_EL1     OFFSET(10) NUMBITS(1) [],
        /// Trap MRS reads of CCSIDR_EL1 at EL1 to EL2
        CCSIDR_EL1    OFFSET(9) NUMBITS(1) [],
        /// Trap MRS reads of APIBKey at EL1 to EL2
        APIBKey       OFFSET(8) NUMBITS(1) [],
        /// Trap MRS reads of APIAKey at EL1 to EL2
        APIAKey       OFFSET(7) NUMBITS(1) [],
        /// Trap MRS reads of APGAKey at EL1 to EL2
        APGAKey       OFFSET(6) NUMBITS(1) [],
        /// Trap MRS reads of APDBKey at EL1 to EL2
        APDBKey       OFFSET(5) NUMBITS(1) [],
        /// Trap MRS reads of APDAKey at EL1 to EL2
        APDAKey       OFFSET(4) NUMBITS(1) [],
        /// Trap MRS reads of AMAIR_EL1 at EL1 to EL2
        AMAIR_EL1     OFFSET(3) NUMBITS(1) [],
        /// Trap MRS reads of AIDR_EL1 at EL1 to EL2
        AIDR_EL1      OFFSET(2) NUMBITS(1) [],
        /// Trap MRS reads of AFSR1_EL1 at EL1 to EL2
        AFSR1_EL1     OFFSET(1) NUMBITS(1) [],
        /// Trap MRS reads of AFSR0_EL1 at EL1 to EL2
        AFSR0_EL1     OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HFGRTR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C1_C1_4", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HFGRTR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C1_C1_4", "x");
}

pub const HFGRTR_EL2: Reg = Reg {};
