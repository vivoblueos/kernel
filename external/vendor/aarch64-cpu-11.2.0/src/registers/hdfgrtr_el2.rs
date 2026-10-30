// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - lingfuyi. <lingfuyi@kylinos.cn>
// https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers/HDFGRTR-EL2--Hypervisor-Debug-Fine-Grained-Read-Trap-Register?lang=en

//! Hypervisor Debug Fine-Grained Read Trap Register - EL2
//!
//! Provides controls for traps of MRS and MRC reads of debug, trace, PMU, and Statistical Profiling
//! System registers.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub HDFGRTR_EL2 [
        /// Trap MRS reads of PMBIDR_EL1 at EL1 using AArch64 to EL2.
        PMBIDR_EL1      OFFSET(63) NUMBITS(1) [],
        /// Trap MRS reads of nPMSNEVFR_EL1 at EL1 using AArch64 to EL2.
        nPMSNEVFR_EL1   OFFSET(62) NUMBITS(1) [],
        /// Trap MRS reads of nBRBDATA at EL1 using AArch64 to EL2.
        nBRBDATA        OFFSET(61) NUMBITS(1) [],
        /// Trap MRS reads of nBRBCTL at EL1 using AArch64 to EL2.
        nBRBCTL         OFFSET(60) NUMBITS(1) [],
        /// Trap MRS reads of nBRBIDR at EL1 using AArch64 to EL2.
        nBRBIDR         OFFSET(59) NUMBITS(1) [],
        /// Trap MRS reads of PMCEIDn_EL0 at EL1 using AArch64 to EL2.
        PMCEIDn_EL0     OFFSET(58) NUMBITS(1) [],
        /// Trap MRS reads of PMUSERENR_EL0 at EL1 using AArch64 to EL2.
        PMUSERENR_EL0   OFFSET(57) NUMBITS(1) [],
        /// Trap MRS reads of TRBTRG_EL1 at EL1 using AArch64 to EL2.
        TRBTRG_EL1      OFFSET(56) NUMBITS(1) [],
        /// Trap MRS reads of TRBSR_EL1 at EL1 using AArch64 to EL2.
        TRBSR_EL1       OFFSET(55) NUMBITS(1) [],
        /// Trap MRS reads of TRBPTR_EL1 at EL1 using AArch64 to EL2.
        TRBPTR_EL1      OFFSET(54) NUMBITS(1) [],
        /// Trap MRS reads of TRBMAR_EL1 at EL1 using AArch64 to EL2.
        TRBMAR_EL1      OFFSET(53) NUMBITS(1) [],
        /// Trap MRS reads of TRBLIMITR_EL1 at EL1 using AArch64 to EL2.
        TRBLIMITR_EL1   OFFSET(52) NUMBITS(1) [],
        /// Trap MRS reads of TRBIDR_EL1 at EL1 using AArch64 to EL2.
        TRBIDR_EL1      OFFSET(51) NUMBITS(1) [],
        /// Trap MRS reads of TRBBASER_EL1 at EL1 using AArch64 to EL2.
        TRBBASER_EL1    OFFSET(50) NUMBITS(1) [],
        // 49: RES0, Reserved bit, write 0
        /// Trap MRS reads of TRCVICTLR at EL1 using AArch64 to EL2.
        TRCVICTLR       OFFSET(48) NUMBITS(1) [],
        /// Trap MRS reads of TRCSTATR at EL1 using AArch64 to EL2.
        TRCSTATR        OFFSET(47) NUMBITS(1) [],
        /// Trap MRS reads of TRCSSCSRn at EL1 using AArch64 to EL2.
        TRCSSCSRn       OFFSET(46) NUMBITS(1) [],
        /// Trap MRS reads of TRCSEQSTR at EL1 using AArch64 to EL2.
        TRCSEQSTR       OFFSET(45) NUMBITS(1) [],
        /// Trap MRS reads of TRCPRGCTLR at EL1 using AArch64 to EL2.
        TRCPRGCTLR      OFFSET(44) NUMBITS(1) [],
        /// Trap MRS reads of TRCOSLSR at EL1 using AArch64 to EL2.
        TRCOSLSR        OFFSET(43) NUMBITS(1) [],
        // 42: RES0, Reserved bit, write 0
        /// Trap MRS reads of TRCIMSPECn at EL1 using AArch64 to EL2.
        TRCIMSPECn      OFFSET(41) NUMBITS(1) [],
        /// Trap MRS reads of TRCID at EL1 using AArch64 to EL2.
        TRCID           OFFSET(40) NUMBITS(1) [],
        // 39-38: RES0, Reserved bit, write 0
        /// Trap MRS reads of TRCCNTVRn at EL1 using AArch64 to EL2.
        TRCCNTVRn       OFFSET(37) NUMBITS(1) [],
        /// Trap MRS reads of TRCCLAIM at EL1 using AArch64 to EL2.
        TRCCLAIM        OFFSET(36) NUMBITS(1) [],
        /// Trap MRS reads of TRCAUXCTLR at EL1 using AArch64 to EL2.
        TRCAUXCTLR      OFFSET(35) NUMBITS(1) [],
        /// Trap MRS reads of TRCAUTHSTATUS at EL1 using AArch64 to EL2.
        TRCAUTHSTATUS   OFFSET(34) NUMBITS(1) [],
        /// Trap MRS reads of TRC at EL1 using AArch64 to EL2.
        TRC             OFFSET(33) NUMBITS(1) [],
        /// Trap MRS reads of PMSLATFR_EL1 at EL1 using AArch64 to EL2.
        PMSLATFR_EL1    OFFSET(32) NUMBITS(1) [],
        /// Trap MRS reads of PMSIRR_EL1 at EL1 using AArch64 to EL2.
        PMSIRR_EL1      OFFSET(31) NUMBITS(1) [],
        /// Trap MRS reads of PMSIDR_EL1 at EL1 using AArch64 to EL2.
        PMSIDR_EL1      OFFSET(30) NUMBITS(1) [],
        /// Trap MRS reads of PMSICR_EL1 at EL1 using AArch64 to EL2.
        PMSICR_EL1      OFFSET(29) NUMBITS(1) [],
        /// Trap MRS reads of PMSFCR_EL1 at EL1 using AArch64 to EL2.
        PMSFCR_EL1      OFFSET(28) NUMBITS(1) [],
        /// Trap MRS reads of PMSEVFR_EL1 at EL1 using AArch64 to EL2.
        PMSEVFR_EL1     OFFSET(27) NUMBITS(1) [],
        /// Trap MRS reads of PMSCR_EL1 at EL1 using AArch64 to EL2.
        PMSCR_EL1       OFFSET(26) NUMBITS(1) [],
        /// Trap MRS reads of PMBSR_EL1 at EL1 using AArch64 to EL2.
        PMBSR_EL1       OFFSET(25) NUMBITS(1) [],
        /// Trap MRS reads of PMBPTR_EL1 at EL1 using AArch64 to EL2.
        PMBPTR_EL1      OFFSET(24) NUMBITS(1) [],
        /// Trap MRS reads of PMBLIMITR_EL1 at EL1 using AArch64 to EL2.
        PMBLIMITR_EL1   OFFSET(23) NUMBITS(1) [],
        /// Trap MRS reads of PMMIR_EL1 at EL1 using AArch64 to EL2.
        PMMIR_EL1       OFFSET(22) NUMBITS(1) [],
        // 21-20: RES0, Reserved bit, write 0
        /// Trap MRS reads of PMSELR_EL0 at EL1 using AArch64 to EL2.
        PMSELR_EL0      OFFSET(19) NUMBITS(1) [],
        /// Trap MRS reads of PMOVS at EL1 using AArch64 to EL2.
        PMOVS           OFFSET(18) NUMBITS(1) [],
        /// Trap MRS reads of PMINTEN at EL1 using AArch64 to EL2.
        PMINTEN         OFFSET(17) NUMBITS(1) [],
        /// Trap MRS reads of PMCNTEN at EL1 using AArch64 to EL2.
        PMCNTEN         OFFSET(16) NUMBITS(1) [],
        /// Trap MRS reads of PMCCNTR_EL0 at EL1 using AArch64 to EL2.
        PMCCNTR_EL0     OFFSET(15) NUMBITS(1) [],
        /// Trap MRS reads of PMCCFILTR_EL0 at EL1 using AArch64 to EL2.
        PMCCFILTR_EL0   OFFSET(14) NUMBITS(1) [],
        /// Trap MRS reads of PMEVTYPERn_EL0 at EL1 using AArch64 to EL2.
        PMEVTYPERn_EL0  OFFSET(13) NUMBITS(1) [],
        /// Trap MRS reads of PMEVCNTRn_EL0 at EL1 using AArch64 to EL2.
        PMEVCNTRn_EL0   OFFSET(12) NUMBITS(1) [],
        /// Trap MRS reads of OSDLR_EL1 at EL1 using AArch64 to EL2.
        OSDLR_EL1       OFFSET(11) NUMBITS(1) [],
        /// Trap MRS reads of OSECCR_EL1 at EL1 using AArch64 to EL2.
        OSECCR_EL1      OFFSET(10) NUMBITS(1) [],
        /// Trap MRS reads of OSLSR_EL1 at EL1 using AArch64 to EL2.
        OSLSR_EL1       OFFSET(9) NUMBITS(1) [],
        // 8: RES0, Reserved bit, write 0
        /// Trap MRS reads of DBGPRCR_EL1 at EL1 using AArch64 to EL2.
        DBGPRCR_EL1     OFFSET(7) NUMBITS(1) [],
        /// Trap MRS reads of DBGAUTHSTATUS_EL1 at EL1 using AArch64 to EL2.
        DBGAUTHSTATUS_EL1 OFFSET(6) NUMBITS(1) [],
        /// Trap MRS reads of DBGCLAIM at EL1 using AArch64 to EL2.
        DBGCLAIM        OFFSET(5) NUMBITS(1) [],
        /// Trap MRS reads of MDSCR_EL1 at EL1 using AArch64 to EL2.
        MDSCR_EL1       OFFSET(4) NUMBITS(1) [],
        /// Trap MRS reads of DBGWVRn_EL1 at EL1 using AArch64 to EL2.
        DBGWVRn_EL1     OFFSET(3) NUMBITS(1) [],
        /// Trap MRS reads of DBGWCRn_EL1 at EL1 using AArch64 to EL2.
        DBGWCRn_EL1     OFFSET(2) NUMBITS(1) [],
        /// Trap MRS reads of DBGBVRn_EL1 at EL1 using AArch64 to EL2.
        DBGBVRn_EL1     OFFSET(1) NUMBITS(1) [],
        /// Trap MRS reads of DBGBCRn_EL1 at EL1 using AArch64 to EL2.
        DBGBCRn_EL1     OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = HDFGRTR_EL2::Register;

    sys_coproc_read_raw!(u64, "S3_4_C3_C1_4", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = HDFGRTR_EL2::Register;

    sys_coproc_write_raw!(u64, "S3_4_C3_C1_4", "x");
}

pub const HDFGRTR_EL2: Reg = Reg {};
