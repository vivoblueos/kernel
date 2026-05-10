// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use tock_registers::{interfaces::*, register_bitfields};

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers//SCTLR-EL1--System-Control-Register--EL1-
register_bitfields! {u64,
    pub SCTLR_EL1 [
        /// Trap IMPLEMENTATION DEFINED functionality. When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// traps EL0 accesses to the encodings reserved for IMPLEMENTATION DEFINED functionality to EL1.
        TIDCP OFFSET(63) NUMBITS(1) [
            DontTrap = 0,
            Trap = 1,
        ],

        /// SP Interrupt Mask enable. When SCTLR_EL1.NMI is 1, controls whether PSTATE.SP acts as an interrupt mask,
        /// and controls the value of PSTATE.ALLINT on taking an exception to EL1.
        SPINTMASK OFFSET(62) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],

        /// Non-maskable Interrupt enable.
        NMI OFFSET(61) NUMBITS(1) [],

        /// Traps instructions executed at EL0 that access TPIDR2_EL0 to EL1, or to EL2 when EL2 is implemented
        /// and enabled for the current Security state and HCR_EL2.TGE is 1.
        /// The exception is reported using EC syndrome value 0x18.
        ENTP2 OFFSET(60) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Tag Checking Store Only.
        TCSO OFFSET(59) NUMBITS(1) [],

        /// When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1}, Tag Checking Store Only in EL0.
        TCSO0 OFFSET(58) NUMBITS(1) [],

        /// Enhanced Privileged Access Never. When PSTATE.PAN is 1, determines whether an EL1 data access to a page
        /// with stage 1 EL0 instruction access permission generates a Permission fault as a result
        /// of the Privileged Access Never mechanism.
        EPAN OFFSET(57) NUMBITS(1) [],

        /// When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// traps execution of an LD64B or ST64B instruction at EL0 to EL1.
        ENALS OFFSET(56) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// traps execution of an ST64BV0 instruction at EL0 to EL1.
        ENAS0 OFFSET(55) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// traps execution of an ST64BV instruction at EL0 to EL1.
        ENASR OFFSET(54) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Enables the Transactional Memory Extension at EL1.
        TME OFFSET(53) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Enables the Transactional Memory Extension at EL0.
        TME0 OFFSET(52) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Forces a trivial implementation of the Transactional Memory Extension at EL1.
        TMT OFFSET(51) NUMBITS(1) [],

        /// Forces a trivial implementation of the Transactional Memory Extension at EL0.
        TMT0 OFFSET(50) NUMBITS(1) [],

        /// TWE Delay. A 4-bit unsigned number that, when SCTLR_EL1.TWEDEn is 1,
        /// encodes the minimum delay in taking a trap of WFE* caused by SCTLR_EL1.nTWE as 2(TWEDEL + 8) cycles.
        TWEDEL OFFSET(46) NUMBITS(4) [],

        /// TWE Delay Enable. Enables a configurable delayed trap of the WFE* instruction caused by SCTLR_EL1.nTWE.
        TWEDEN OFFSET(45) NUMBITS(1) [],

        /// Default PSTATE.SSBS value on Exception Entry.
        DSSBS OFFSET(44) NUMBITS(1) [],

        /// When SCR_EL3.ATA == 1 and HCR_EL2.ATA == 1, controls access to Allocation Tags and Tag Check operations in EL1.
        ATA OFFSET(43) NUMBITS(1) [],

        /// When SCR_EL3.ATA == 1, HCR_EL2.ATA == 1, and the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// controls access to Allocation Tags and Tag Check operations in EL0.
        ATA0 OFFSET(42) NUMBITS(1) [],

        /// Tag Check Fault in EL1. Controls the effect of Tag Check Faults due to Loads and Stores in EL1.
        TCF OFFSET(40) NUMBITS(2) [],

        /// Tag Check Fault in EL0. When the Effective value of HCR_EL2.{E2H, TGE} is not {1, 1},
        /// controls the effect of Tag Check Faults due to Loads and Stores in EL0.
        TCF0 OFFSET(38) NUMBITS(2) [],

        /// When synchronous exceptions are not being generated by Tag Check Faults,
        /// this field controls whether on exception entry into EL1,
        /// all Tag Check Faults due to instructions executed before exception entry,
        /// that are reported asynchronously, are synchronized into TFSRE0_EL1 and TFSR_EL1 registers.
        ITFSB OFFSET(37) NUMBITS(1) [],

        /// When FEAT_BTI is implemented:
        /// Configures the Branch Type compatibility of the implicit BTI behavior for the following instructions at EL1:
        /// PACIASP.
        /// PACIBSP.
        /// If FEAT_PAuth_LR is implemented, PACIASPPC.
        /// If FEAT_PAuth_LR is implemented, PACIBSPPC.
        BT1 OFFSET(36) NUMBITS(1) [],

        /// When FEAT_BTI is implemented:
        /// Configures the Branch Type compatibility of the implicit BTI behavior for the following instructions at EL0:
        /// PACIASP.
        /// PACIBSP.
        /// If FEAT_PAuth_LR is implemented, PACIASPPC.
        /// If FEAT_PAuth_LR is implemented, PACIBSPPC.
        BT0 OFFSET(35) NUMBITS(1) [],

        /// When FEAT_FPMR is implemented:
        /// Enables direct and indirect accesses to FPMR from EL0.
        ENFPM OFFSET(34) NUMBITS(1) [],

        /// When FEAT_MOPS is implemented and !ELIsInHost(EL0):
        /// Memory Copy and Memory Set instructions Enable. Enables execution of the Memory Copy
        /// and Memory Set instructions at EL0.
        MSCEN OFFSET(33) NUMBITS(1) [],

        /// Controls cache maintenance instruction permission for the following instructions executed at EL0.
        CMOW OFFSET(32) NUMBITS(1) [],

        /// When FEAT_PAuth is implemented:
        /// Controls enabling of pointer authentication of instruction addresses, using the APIAKey_EL1 key,
        /// in the EL1&0 translation regime.
        ENIA OFFSET(31) NUMBITS(1) [
            Disable = 0,
            Enabled = 1,
        ],

        /// When FEAT_PAuth is implemented:
        /// Controls enabling of pointer authentication of instruction addresses, using the APIBKey_EL1 key,
        /// in the EL1&0 translation regime.
        ENIB OFFSET(30) NUMBITS(1) [
            Disable = 0,
            Enabled = 1,
        ],

        /// When FEAT_LSMAOC is implemented:
        /// Load Multiple and Store Multiple Atomicity and Ordering Enable
        LSMAOE OFFSET(29) NUMBITS(1) [
            Disable = 0,
            Enabled = 1,
        ],

        /// When FEAT_LSMAOC is implemented:
        /// No Trap Load Multiple and Store Multiple to Device-nGRE/Device-nGnRE/Device-nGnRnE memory.
        NTLSMD OFFSET(28) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When FEAT_PAuth is implemented:
        /// Controls enabling of pointer authentication of instruction addresses, using the APDAKey_EL1 key,
        /// in the EL1&0 translation regime.
        ENDA OFFSET(27) NUMBITS(1) [
            Disable = 0,
            Enabled = 1,
        ],

        /// Traps EL0 execution of cache maintenance instructions to EL1, from AArch64 state only.
        UCI OFFSET(26) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When FEAT_MixedEnd is implemented:
        /// Endianness of data accesses at EL1, and stage 1 translation table walks in the EL1&0 translation regime.
        EE OFFSET(25) NUMBITS(1) [
            LittleEndian = 0,
            BigEndian = 1,
        ],

        /// Endianness of data accesses at EL0.
        E0E OFFSET(24) NUMBITS(1) [
            LittleEndian = 0,
            BigEndian = 1,
        ],

        /// When FEAT_PAN is implemented:
        /// Set Privileged Access Never, on taking an exception to EL1.
        SPAN OFFSET(23) NUMBITS(1) [
            Set = 0,
            Unset = 1
        ],

        /// When FEAT_ExS is implemented:
        /// Exception Entry is Context Synchronizing.
        EIS OFFSET(22) NUMBITS(1) [
            NotContextSynchronizingEvent = 0,
            ContextSynchronizingEvent = 1
        ],

        /// When FEAT_IESB is implemented:
        /// Implicit Error Synchronization event enable. Possible values are
        IESB OFFSET(21) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// When FEAT_CSV2_2 is implemented or FEAT_CSV2_1p2 is implemented:
        //  Trap EL0 Access to the SCXTNUM_EL0 register, when EL0 is using AArch64.
        TSCXT OFFSET(20) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Write permission implies XN (Execute-never). For the EL1&0 translation regime, this bit can force
        /// all memory regions that are writable to be treated as XN.
        WXN OFFSET(19) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// Traps EL0 execution of WFE instructions to EL1, or to EL2 when it is implemented
        /// and enabled for the current Security state and HCR_EL2.TGE is 1, from both Execution states,
        /// reported using EC syndrome value 0x01.
        NTWE OFFSET(18) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 execution of WFI instructions to EL1, or to EL2 when it is implemented
        /// and enabled for the current Security state and HCR_EL2.TGE is 1, from both Execution states,
        /// reported using EC syndrome value 0x01.
        NTWI OFFSET(16) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 accesses to the CTR_EL0 to EL1, or to EL2 when it is implemented
        /// and enabled for the current Security state and HCR_EL2.TGE is 1, from AArch64 state only,
        ///  reported using EC syndrome value 0x18.
        UCT OFFSET(15) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 execution of DC ZVA instructions to EL1, or to EL2 when it is implemented
        /// and enabled for the current Security state and HCR_EL2.TGE is 1, from AArch64 state only,
        /// reported using EC syndrome value 0x18.
        DZE OFFSET(14) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When FEAT_PAuth is implemented:
        /// Controls enabling of pointer authentication of instruction addresses,
        /// using the APDBKey_EL1 key, in the EL1&0 translation regime.
        ENDB OFFSET(13) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Instruction access Cacheability control, for accesses at EL0 and EL1
        I OFFSET(12) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// When FEAT_ExS is implemented:
        /// Exception Exit is Context Synchronizing.
        EOS OFFSET(11) NUMBITS(1) [
            NotContextSynchronizingEvent = 0,
            ContextSynchronizingEvent = 1
        ],

        /// When FEAT_SPECRES is implemented:
        /// Enable EL0 access to the following System instructions:
        /// CFPRCTX, DVPRCTX and CPPRCTX instructions.
        /// If FEAT_SPECRES2 is implemented, COSPRCTX.
        /// CFP RCTX, DVP RCTX and CPP RCTX instructions.
        /// If FEAT_SPECRES2 is implemented, COSP RCTX.
        ENRCTX OFFSET(10) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// User Mask Access.
        /// Traps EL0 execution of MSR and MRS instructions that access the PSTATE.{D, A, I, F} masks to EL1,
        /// or to EL2 when it is implemented and enabled for the current Security state and HCR_EL2.TGE is 1,
        /// from AArch64 state only, reported using EC syndrome value 0x18.
        UMA OFFSET(9) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// When EL0 is capable of using AArch32:
        /// SETEND instruction disable. Disables SETEND instructions at EL0 using AArch32.
        SED OFFSET(8) NUMBITS(1) [
            Ensable = 0,
            Disable = 1
        ],

        /// When EL0 is capable of using AArch32:
        /// IT Disable. Disables some uses of IT instructions at EL0 using AArch32.
        ITD OFFSET(7) NUMBITS(1) [
            Ensable = 0,
            Disable = 1
        ],

        /// When FEAT_LSE2 is implemented:
        /// Non-aligned access. This bit controls generation of Alignment faults at EL1 and EL0 under certain conditions.
        NAA OFFSET(6) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// When EL0 is capable of using AArch32:
        /// System instruction memory barrier enable.
        /// Enables accesses to the DMB, DSB, and ISB System instructions in the (coproc==0b1111) encoding space from EL0:
        /// Disable: EL0 execution of the CP15DMB, CP15DSB, and CP15ISB instructions is UNDEFINED
        /// Enable: EL0 execution of the CP15DMB, CP15DSB, and CP15ISB instructions is enabled.
        CP15BEN OFFSET(5) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// SP Alignment check enable for EL0.
        /// When set to 1, if a load or store instruction executed at EL0 uses the SP as the base address
        /// and the SP is not aligned to a 16-byte boundary, then an SP alignment fault exception is generated.
        SA0 OFFSET(4) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// SP Alignment check enable.
        /// When set to 1, if a load or store instruction executed at EL1 uses the SP as the base address
        /// and the SP is not aligned to a 16-byte boundary, then an SP alignment fault exception is generated.
        SA OFFSET(3) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Stage 1 Cacheability control, for data accesses.
        C OFFSET(2) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// Alignment check enable. This is the enable bit for Alignment fault checking at EL1 and EL0.
        A OFFSET(1) NUMBITS(1) [
            DisableAlignment  = 0,
            EnableAlignment  = 1
        ],

        /// MMU enable for EL1&0 stage 1 address translation.
        M OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ]
    ]
}

pub struct SctlrEl1;

impl Readable for SctlrEl1 {
    type T = u64;
    type R = SCTLR_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, sctlr_el1",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for SctlrEl1 {
    type T = u64;
    type R = SCTLR_EL1::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr sctlr_el1, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const SCTLR_EL1: SctlrEl1 = SctlrEl1 {};
