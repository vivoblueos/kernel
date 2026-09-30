// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HFGWTR-EL2--Hypervisor-Fine-Grained-Write-Trap-Register?lang=en

//! Hypervisor Fine-Grained Write Trap Register - EL2
//!
//! Provides controls for traps of MSR and MCR writes of System registers

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HFGWTR_EL2 [
        /// Trap MSR writes of AMAIR2_EL1 at EL1 to EL2
        nAMAIR2_EL1   OFFSET(63) NUMBITS(1) [],
        /// Trap MSR writes of MAIR2_EL1 at EL1 to EL2
        nMAIR2_EL1    OFFSET(62) NUMBITS(1) [],
        /// Trap MSR writes of S2POR_EL1 at EL1 to EL2
        nS2POR_EL1    OFFSET(61) NUMBITS(1) [],
        /// Trap MSR writes of POR_EL1 at EL1 to EL2
        nPOR_EL1      OFFSET(60) NUMBITS(1) [],
        /// Trap MSR writes of POR_EL0 at EL1 to EL2
        nPOR_EL0      OFFSET(59) NUMBITS(1) [],
        /// Trap MSR writes of PIR_EL1 at EL1 to EL2
        nPIR_EL1      OFFSET(58) NUMBITS(1) [],
        /// Trap MSR writes of PIRE0_EL1 at EL1 to EL2
        nPIRE0_EL1    OFFSET(57) NUMBITS(1) [],
        /// Trap MSR writes of RCWMASK_EL1 at EL1 to EL2
        nRCWMASK_EL1  OFFSET(56) NUMBITS(1) [],
        /// Trap MSR writes of TPIDR2_EL0 at EL1 to EL2
        nTPIDR2_EL0   OFFSET(55) NUMBITS(1) [],
        /// Trap MSR writes of SMPRI_EL1 at EL1 to EL2
        nSMPRI_EL1    OFFSET(54) NUMBITS(1) [],
        /// Trap MSR writes of GCS_EL1 at EL1 to EL2
        nGCS_EL1      OFFSET(53) NUMBITS(1) [],
        /// Trap MSR writes of GCS_EL0 at EL1 to EL2
        nGCS_EL0      OFFSET(52) NUMBITS(1) [],
        // 51: RES0 (reserved)
        /// Trap MSR writes of ACCDATA_EL1 at EL1 to EL2
        nACCDATA_EL1  OFFSET(50) NUMBITS(1) [],
        /// Trap MSR writes of ERXADDR_EL1 at EL1 to EL2
        ERXADDR_EL1   OFFSET(49) NUMBITS(1) [],
        /// Trap MSR writes of ERXPFGCDN_EL1 at EL1 to EL2
        ERXPFGCDN_EL1 OFFSET(48) NUMBITS(1) [],
        /// Trap MSR writes of ERXPFGCTL_EL1 at EL1 to EL2
        ERXPFGCTL_EL1 OFFSET(47) NUMBITS(1) [],
        // 46: RES0 (reserved)
        /// Trap MSR writes of ERXMISCn_EL1 at EL1 to EL2
        ERXMISCn_EL1  OFFSET(45) NUMBITS(1) [],
        /// Trap MSR writes of ERXSTATUS_EL1 at EL1 to EL2
        ERXSTATUS_EL1 OFFSET(44) NUMBITS(1) [],
        /// Trap MSR writes of ERXCTLR_EL1 at EL1 to EL2
        ERXCTLR_EL1   OFFSET(43) NUMBITS(1) [],
        // 42: RES0 (reserved)
        /// Trap MSR writes of ERRSELR_EL1 at EL1 to EL2
        ERRSELR_EL1   OFFSET(41) NUMBITS(1) [],
        // 40: RES0 (reserved)
        /// Trap MSR writes of ICC_IGRPENn_EL1 at EL1 to EL2
        ICC_IGRPENn_EL1 OFFSET(39) NUMBITS(1) [],
        /// Trap MSR writes of VBAR_EL1 at EL1 to EL2
        VBAR_EL1      OFFSET(38) NUMBITS(1) [],
        /// Trap MSR writes of TTBR1_EL1 at EL1 to EL2
        TTBR1_EL1     OFFSET(37) NUMBITS(1) [],
        /// Trap MSR writes of TTBR0_EL1 at EL1 to EL2
        TTBR0_EL1     OFFSET(36) NUMBITS(1) [],
        /// Trap MSR writes of TPIDR_EL0 at EL1 to EL2
        TPIDR_EL0     OFFSET(35) NUMBITS(1) [],
        /// Trap MSR writes of TPIDRRO_EL0 at EL1 to EL2
        TPIDRRO_EL0   OFFSET(34) NUMBITS(1) [],
        /// Trap MSR writes of TPIDR_EL1 at EL1 to EL2
        TPIDR_EL1     OFFSET(33) NUMBITS(1) [],
        /// Trap MSR writes of TCR_EL1 at EL1 to EL2
        TCR_EL1       OFFSET(32) NUMBITS(1) [],
        /// Trap MSR writes of SCXTNUM_EL0 at EL1 to EL2
        SCXTNUM_EL0   OFFSET(31) NUMBITS(1) [],
        /// Trap MSR writes of SCXTNUM_EL1 at EL1 to EL2
        SCXTNUM_EL1   OFFSET(30) NUMBITS(1) [],
        /// Trap MSR writes of SCTLR_EL1 at EL1 to EL2
        SCTLR_EL1     OFFSET(29) NUMBITS(1) [],
        // 28: RES0 (reserved)
        /// Trap MSR writes of PAR_EL1 at EL1 to EL2
        PAR_EL1       OFFSET(27) NUMBITS(1) [],
        // 26: RES0 (reserved)
        // 25: RES0 (reserved)
        /// Trap MSR writes of MAIR_EL1 at EL1 to EL2
        MAIR_EL1      OFFSET(24) NUMBITS(1) [],
        /// Trap MSR writes of LORSA_EL1 at EL1 to EL2
        LORSA_EL1     OFFSET(23) NUMBITS(1) [],
        /// Trap MSR writes of LORN_EL1 at EL1 to EL2
        LORN_EL1      OFFSET(22) NUMBITS(1) [],
        // 21: RES0 (reserved)
        /// Trap MSR writes of LOREA_EL1 at EL1 to EL2
        LOREA_EL1     OFFSET(20) NUMBITS(1) [],
        /// Trap MSR writes of LORC_EL1 at EL1 to EL2
        LORC_EL1      OFFSET(19) NUMBITS(1) [],
        // 18: RES0 (reserved)
        /// Trap MSR writes of FAR_EL1 at EL1 to EL2
        FAR_EL1       OFFSET(17) NUMBITS(1) [],
        /// Trap MSR writes of ESR_EL1 at EL1 to EL2
        ESR_EL1       OFFSET(16) NUMBITS(1) [],
        // 15: RES0 (reserved)
        // 14: RES0 (reserved)
        /// Trap MSR writes of CSSELR_EL1 at EL1 to EL2
        CSSELR_EL1    OFFSET(13) NUMBITS(1) [],
        /// Trap MSR writes of CPACR_EL1 at EL1 to EL2
        CPACR_EL1     OFFSET(12) NUMBITS(1) [],
        /// Trap MSR writes of CONTEXTIDR_EL1 at EL1 to EL2
        CONTEXTIDR_EL1 OFFSET(11) NUMBITS(1) [],
        // 10: RES0 (reserved)
        // 9: RES0 (reserved)
        /// Trap MSR writes of APIBKey at EL1 to EL2
        APIBKey       OFFSET(8) NUMBITS(1) [],
        /// Trap MSR writes of APIAKey at EL1 to EL2
        APIAKey       OFFSET(7) NUMBITS(1) [],
        /// Trap MSR writes of APGAKey at EL1 to EL2
        APGAKey       OFFSET(6) NUMBITS(1) [],
        /// Trap MSR writes of APDBKey at EL1 to EL2
        APDBKey       OFFSET(5) NUMBITS(1) [],
        /// Trap MSR writes of APDAKey at EL1 to EL2
        APDAKey       OFFSET(4) NUMBITS(1) [],
        /// Trap MSR writes of AMAIR_EL1 at EL1 to EL2
        AMAIR_EL1     OFFSET(3) NUMBITS(1) [],
        // 2: RES0 (reserved)
        /// Trap MSR writes of AFSR1_EL1 at EL1 to EL2
        AFSR1_EL1     OFFSET(1) NUMBITS(1) [],
        /// Trap MSR writes of AFSR0_EL1 at EL1 to EL2
        AFSR0_EL1     OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HFGWTR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C1_C1_5", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HFGWTR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C1_C1_5", "x");
}

pub const HFGWTR_EL2: Reg = Reg {};
