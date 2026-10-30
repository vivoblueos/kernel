// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HDFGWTR-EL2--Hypervisor-Debug-Fine-Grained-Write-Trap-Register?lang=en

//! Hypervisor Debug Fine-Grained Write Trap Register - EL2
//!
//! Provides controls for traps of MSR and MCR writes of debug, trace, PMU, and Statistical
//! Profiling System registers.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HDFGWTR_EL2 [
        // 63: RES0, Reserved bit, write 0
        /// Trap MSR writes of nPMSNEVFR_EL1 at EL1 using AArch64 to EL2.
        nPMSNEVFR_EL1   OFFSET(62) NUMBITS(1) [],
        /// Trap MSR writes of nBRBDATA at EL1 using AArch64 to EL2.
        nBRBDATA        OFFSET(61) NUMBITS(1) [],
        /// Trap MSR writes of nBRBCTL at EL1 using AArch64 to EL2.
        nBRBCTL         OFFSET(60) NUMBITS(1) [],
        // 59-58: RES0, Reserved bit, write 0
        /// Trap MSR writes of PMUSERENR_EL0 at EL1 using AArch64 to EL2.
        PMUSERENR_EL0   OFFSET(57) NUMBITS(1) [],
        /// Trap MSR writes of TRBTRG_EL1 at EL1 using AArch64 to EL2.
        TRBTRG_EL1      OFFSET(56) NUMBITS(1) [],
        /// Trap MSR writes of TRBSR_EL1 at EL1 using AArch64 to EL2.
        TRBSR_EL1       OFFSET(55) NUMBITS(1) [],
        /// Trap MSR writes of TRBPTR_EL1 at EL1 using AArch64 to EL2.
        TRBPTR_EL1      OFFSET(54) NUMBITS(1) [],
        /// Trap MSR writes of TRBMAR_EL1 at EL1 using AArch64 to EL2.
        TRBMAR_EL1      OFFSET(53) NUMBITS(1) [],
        /// Trap MSR writes of TRBLIMITR_EL1 at EL1 using AArch64 to EL2.
        TRBLIMITR_EL1   OFFSET(52) NUMBITS(1) [],
        // 51: RES0, Reserved bit, write 0
        /// Trap MSR writes of TRBBASER_EL1 at EL1 using AArch64 to EL2.
        TRBBASER_EL1    OFFSET(50) NUMBITS(1) [],
        /// Trap MSR writes of TRFCR_EL1 at EL1 using AArch64 to EL2.
        TRFCR_EL1       OFFSET(49) NUMBITS(1) [],
        /// Trap MSR writes of TRCVICTLR at EL1 using AArch64 to EL2.
        TRCVICTLR       OFFSET(48) NUMBITS(1) [],
        // 47: RES0, Reserved bit, write 0
        /// Trap MSR writes of TRCSSCSRn at EL1 using AArch64 to EL2.
        TRCSSCSRn       OFFSET(46) NUMBITS(1) [],
        /// Trap MSR writes of TRCSEQSTR at EL1 using AArch64 to EL2.
        TRCSEQSTR       OFFSET(45) NUMBITS(1) [],
        /// Trap MSR writes of TRCPRGCTLR at EL1 using AArch64 to EL2.
        TRCPRGCTLR      OFFSET(44) NUMBITS(1) [],
        // 43: RES0, Reserved bit, write 0
        /// Trap MSR writes of TRCOSLAR at EL1 using AArch64 to EL2.
        TRCOSLAR        OFFSET(42) NUMBITS(1) [],
        /// Trap MSR writes of TRCIMSPECn at EL1 using AArch64 to EL2.
        TRCIMSPECn      OFFSET(41) NUMBITS(1) [],
        // 40-38: RES0, Reserved bit, write 0
        /// Trap MSR writes of TRCCNTVRn at EL1 using AArch64 to EL2.
        TRCCNTVRn       OFFSET(37) NUMBITS(1) [],
        /// Trap MSR writes of TRCCLAIM at EL1 using AArch64 to EL2.
        TRCCLAIM        OFFSET(36) NUMBITS(1) [],
        /// Trap MSR writes of TRCAUXCTLR at EL1 using AArch64 to EL2.
        TRCAUXCTLR      OFFSET(35) NUMBITS(1) [],
        // 34: RES0, Reserved bit, write 0
        /// Trap MSR writes of TRC at EL1 using AArch64 to EL2.
        TRC             OFFSET(33) NUMBITS(1) [],
        /// Trap MSR writes of PMSLATFR_EL1 at EL1 using AArch64 to EL2.
        PMSLATFR_EL1    OFFSET(32) NUMBITS(1) [],
        /// Trap MSR writes of PMSIRR_EL1 at EL1 using AArch64 to EL2.
        PMSIRR_EL1      OFFSET(31) NUMBITS(1) [],
        // 30: RES0, Reserved bit, write 0
        /// Trap MSR writes of PMSICR_EL1 at EL1 using AArch64 to EL2.
        PMSICR_EL1      OFFSET(29) NUMBITS(1) [],
        /// Trap MSR writes of PMSFCR_EL1 at EL1 using AArch64 to EL2.
        PMSFCR_EL1      OFFSET(28) NUMBITS(1) [],
        /// Trap MSR writes of PMSEVFR_EL1 at EL1 using AArch64 to EL2.
        PMSEVFR_EL1     OFFSET(27) NUMBITS(1) [],
        /// Trap MSR writes of PMSCR_EL1 at EL1 using AArch64 to EL2.
        PMSCR_EL1       OFFSET(26) NUMBITS(1) [],
        /// Trap MSR writes of PMBSR_EL1 at EL1 using AArch64 to EL2.
        PMBSR_EL1       OFFSET(25) NUMBITS(1) [],
        /// Trap MSR writes of PMBPTR_EL1 at EL1 using AArch64 to EL2.
        PMBPTR_EL1      OFFSET(24) NUMBITS(1) [],
        /// Trap MSR writes of PMBLIMITR_EL1 at EL1 using AArch64 to EL2.
        PMBLIMITR_EL1   OFFSET(23) NUMBITS(1) [],
        // 22: RES0, Reserved bit, write 0
        /// Trap MSR writes of PMCR_EL0 at EL1 using AArch64 to EL2.
        PMCR_EL0        OFFSET(21) NUMBITS(1) [],
        /// Trap MSR writes of PMSWINC_EL0 at EL1 using AArch64 to EL2.
        PMSWINC_EL0     OFFSET(20) NUMBITS(1) [],
        /// Trap MSR writes of PMSELR_EL0 at EL1 using AArch64 to EL2.
        PMSELR_EL0      OFFSET(19) NUMBITS(1) [],
        /// Trap MSR writes of PMOVS at EL1 using AArch64 to EL2.
        PMOVS           OFFSET(18) NUMBITS(1) [],
        /// Trap MSR writes of PMINTEN at EL1 using AArch64 to EL2.
        PMINTEN         OFFSET(17) NUMBITS(1) [],
        /// Trap MSR writes of PMCNTEN at EL1 using AArch64 to EL2.
        PMCNTEN         OFFSET(16) NUMBITS(1) [],
        /// Trap MSR writes of PMCCNTR_EL0 at EL1 using AArch64 to EL2.
        PMCCNTR_EL0     OFFSET(15) NUMBITS(1) [],
        /// Trap MSR writes of PMCCFILTR_EL0 at EL1 using AArch64 to EL2.
        PMCCFILTR_EL0   OFFSET(14) NUMBITS(1) [],
        /// Trap MSR writes of PMEVTYPERn_EL0 at EL1 using AArch64 to EL2.
        PMEVTYPERn_EL0  OFFSET(13) NUMBITS(1) [],
        /// Trap MSR writes of PMEVCNTRn_EL0 at EL1 using AArch64 to EL2.
        PMEVCNTRn_EL0   OFFSET(12) NUMBITS(1) [],
        /// Trap MSR writes of OSDLR_EL1 at EL1 using AArch64 to EL2.
        OSDLR_EL1       OFFSET(11) NUMBITS(1) [],
        /// Trap MSR writes of OSECCR_EL1 at EL1 using AArch64 to EL2.
        OSECCR_EL1      OFFSET(10) NUMBITS(1) [],
        // 9: RES0, Reserved bit, write 0
        /// Trap MSR writes of OSLAR_EL1 at EL1 using AArch64 to EL2.
        OSLAR_EL1       OFFSET(8) NUMBITS(1) [],
        /// Trap MSR writes of DBGPRCR_EL1 at EL1 using AArch64 to EL2.
        DBGPRCR_EL1     OFFSET(7) NUMBITS(1) [],
        // 6: RES0, Reserved bit, write 0
        /// Trap MSR writes of DBGCLAIM at EL1 using AArch64 to EL2.
        DBGCLAIM        OFFSET(5) NUMBITS(1) [],
        /// Trap MSR writes of MDSCR_EL1 at EL1 using AArch64 to EL2.
        MDSCR_EL1       OFFSET(4) NUMBITS(1) [],
        /// Trap MSR writes of DBGWVRn_EL1 at EL1 using AArch64 to EL2.
        DBGWVRn_EL1     OFFSET(3) NUMBITS(1) [],
        /// Trap MSR writes of DBGWCRn_EL1 at EL1 using AArch64 to EL2.
        DBGWCRn_EL1     OFFSET(2) NUMBITS(1) [],
        /// Trap MSR writes of DBGBVRn_EL1 at EL1 using AArch64 to EL2.
        DBGBVRn_EL1     OFFSET(1) NUMBITS(1) [],
        /// Trap MSR writes of DBGBCRn_EL1 at EL1 using AArch64 to EL2.
        DBGBCRn_EL1     OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HDFGWTR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C3_C1_5", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HDFGWTR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C3_C1_5", "x");
}

pub const HDFGWTR_EL2: Reg = Reg {};
