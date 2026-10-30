// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2025 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Berkus Decker <berkus+github@metta.systems>
//   - Yan Tan <tanyan@kylinos.cn>

//! Exception Syndrome Register - EL1
//!
//! Holds syndrome information for an exception taken to EL1.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub ESR_EL1 [
        /// Exception Class. Indicates the reason for the exception that this register holds
        /// information about.
        ///
        /// For each EC value, the table references a subsection that gives information about:
        ///   - The cause of the exception, for example the configuration required to enable the
        ///     trap.
        ///   - The encoding of the associated ISS.
        EC  OFFSET(26) NUMBITS(6) [
            /// Unknown reason
            Unknown = 0b00_0000,
            /// Trapped WF* instruction execution
            TrappedWFIorWFE = 0b00_0001,
            /// Trapped MCR or MRC access with (coproc==0b1111) (FEAT_AA32)
            TrappedMCRorMRC = 0b00_0011,
            /// Trapped MCRR or MRRC access with (coproc==0b1111) (FEAT_AA32)
            TrappedMCRRorMRRC = 0b00_0100,
            /// Trapped MCR or MRC access with (coproc==0b1110) (FEAT_AA32)
            TrappedMCRorMRC2 = 0b00_0101,
            /// Trapped LDC or STC access (FEAT_AA32)
            TrappedLDCorSTC = 0b00_0110,
            /// Access to SME, SVE, Advanced SIMD or floating-point functionality trapped
            TrappedFP = 0b00_0111,
            /// Trapped execution of any instruction not covered by other EC values (FEAT_LS64)
            TrappedNotCovered = 0b00_1010,
            /// Trapped MRRC access with (coproc==0b1110) (FEAT_AA32)
            TrappedMRRC = 0b00_1100,
            /// Branch Target Exception (FEAT_BTI)
            BranchTarget = 0b00_1101,
            /// Illegal Execution state (FEAT_BTI)
            IllegalExecutionState = 0b00_1110,
            /// SVC instruction execution in AArch32 state (FEAT_AA32)
            SVC32 = 0b01_0001,
            /// Trapped MSRR, MRRS or System instruction execution in AArch64 state (FEAT_SYSREG128/FEAT_SYSINSTR128)
            TrappedMSRR_MRRS = 0b01_0100,
            /// SVC instruction execution in AArch64 state
            SVC64 = 0b01_0101,
            /// HVC instruction execution in AArch64 state
            HVC64 = 0b01_0110,
            /// SMC instruction execution in AArch64 state
            SMC64 = 0b01_0111,
            /// Trapped MSR, MRS or System instruction execution in AArch64 state
            TrappedMsrMrs = 0b01_1000,
            /// Access to SVE functionality trapped (FEAT_SVE)
            TrappedSve = 0b01_1001,
            /// Exception from TSTART instruction (FEAT_TME)
            TrappedTSTART = 0b01_1011,
            /// Exception from a PAC Fail (FEAT_FPAC)
            PointerAuth = 0b01_1100,
            /// Access to SME functionality trapped (FEAT_SME)
            TrappedSME = 0b01_1101,
            /// Instruction Abort from a lower Exception level
            InstrAbortLowerEL = 0b10_0000,
            /// Instruction Abort taken without a change in Exception level
            InstrAbortCurrentEL = 0b10_0001,
            /// PC alignment fault exception
            PCAlignmentFault = 0b10_0010,
            /// Data Abort exception from a lower Exception level
            DataAbortLowerEL = 0b10_0100,
            /// Data Abort exception without a change in Exception level
            DataAbortCurrentEL = 0b10_0101,
            /// SP alignment fault exception
            SPAlignmentFault = 0b10_0110,
            /// Memory Operation Exception (FEAT_MOPS)
            MemoryOperationException = 0b10_0111,
            /// Trapped floating-point exception taken from AArch32 state (FEAT_AA32)
            TrappedFP32 = 0b10_1000,
            /// Trapped floating-point exception taken from AArch64 state
            TrappedFP64 = 0b10_1100,
            /// GCS exception (FEAT_GCS)
            GCSException = 0b10_1101,
            /// SError exception
            SError = 0b10_1111,
            /// Breakpoint exception from a lower Exception level
            BreakpointLowerEL = 0b11_0000,
            /// Breakpoint exception taken without a change in Exception level
            BreakpointCurrentEL = 0b11_0001,
            /// Software Step exception from a lower Exception level
            SoftwareStepLowerEL = 0b11_0010,
            /// Software Step exception taken without a change in Exception level
            SoftwareStepCurrentEL = 0b11_0011,
            /// Watchpoint exception from a lower Exception level
            WatchpointLowerEL = 0b11_0100,
            /// Watchpoint exception taken without a change in Exception level
            WatchpointCurrentEL = 0b11_0101,
            /// BKPT instruction execution in AArch32 state (FEAT_AA32)
            Bkpt32 = 0b11_1000,
            /// BRK instruction execution in AArch64 state
            Brk64 = 0b11_1100,
            /// Profiling exception (FEAT_EBEP/FEAT_SPE_EXC/FEAT_TRBE_EXC)
            ProfilingException = 0b11_1101
        ],

        /// Instruction Length for synchronous exceptions.
        IL  OFFSET(25) NUMBITS(1) [],

        /// Instruction Specific Syndrome. Architecturally, this field can be defined independently
        /// for each defined Exception class. However, in practice, some ISS encodings are used for
        /// more than one Exception class.
        ISS OFFSET(0)  NUMBITS(25) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ESR_EL1::Register;

    sys_coproc_read_raw!(u64, "ESR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ESR_EL1::Register;

    sys_coproc_write_raw!(u64, "ESR_EL1", "x");
}

pub const ESR_EL1: Reg = Reg {};
