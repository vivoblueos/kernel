// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! System Control Register - EL1
//!
//! Provides top level control of the system, including its memory system, at EL1 and EL0.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub SCTLR_EL1 [
        /// Traps EL0 execution of cache maintenance instructions to EL1, from AArch64 state only.
        ///
        /// 0 Any attempt to execute a DC CVAU, DC CIVAC, DC CVAC, DC CVAP, or IC IVAU
        ///   instruction at EL0 using AArch64 is trapped to EL1.
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        ///
        /// If the Point of Coherency is before any level of data cache, it is IMPLEMENTATION DEFINED whether
        /// the execution of any data or unified cache clean, or clean and invalidate instruction that operates by
        /// VA to the point of coherency can be trapped when the value of this control is 1.
        ///
        /// If the Point of Unification is before any level of data cache, it is IMPLEMENTATION DEFINED whether
        /// the execution of any data or unified cache clean by VA to the point of unification instruction can be
        /// trapped when the value of this control is 1.
        ///
        /// If the Point of Unification is before any level of instruction cache, it is IMPLEMENTATION DEFINED
        /// whether the execution of any instruction cache invalidate by VA to the point of unification
        /// instruction can be trapped when the value of this control is 1.
        UCI OFFSET(26) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Endianness of data accesses at EL1, and stage 1 translation table walks in the EL1&0 translation regime.
        ///
        /// 0 Explicit data accesses at EL1, and stage 1 translation table walks in the EL1&0
        ///   translation regime are little-endian.
        /// 1 Explicit data accesses at EL1, and stage 1 translation table walks in the EL1&0
        ///   translation regime are big-endian.
        ///
        /// If an implementation does not provide Big-endian support at Exception Levels higher than EL0, this
        /// bit is RES 0.
        ///
        /// If an implementation does not provide Little-endian support at Exception Levels higher than EL0,
        /// this bit is RES 1.
        ///
        /// The EE bit is permitted to be cached in a TLB.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on the PE.
        EE OFFSET(25) NUMBITS(1) [
            LittleEndian = 0,
            BigEndian = 1,
        ],

        /// Endianness of data accesses at EL0.
        ///
        /// 0 Explicit data accesses at EL0 are little-endian.
        ///
        /// 1 Explicit data accesses at EL0 are big-endian.
        ///
        /// If an implementation only supports Little-endian accesses at EL0 then this bit is RES 0. This option
        /// is not permitted when SCTLR_EL1.EE is RES 1.
        ///
        /// If an implementation only supports Big-endian accesses at EL0 then this bit is RES 1. This option is
        /// not permitted when SCTLR_EL1.EE is RES 0.
        ///
        /// This bit has no effect on the endianness of LDTR , LDTRH , LDTRSH , LDTRSW , STTR , and STTRH instructions
        /// executed at EL1.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        E0E OFFSET(24) NUMBITS(1) [
            LittleEndian = 0,
            BigEndian = 1,
        ],

        /// Write permission implies XN (Execute-never). For the EL1&0 translation regime, this bit can force
        /// all memory regions that are writable to be treated as XN.
        ///
        /// 0 This control has no effect on memory access permissions.
        ///
        /// 1 Any region that is writable in the EL1&0 translation regime is forced to XN for accesses
        ///   from software executing at EL1 or EL0.
        ///
        /// The WXN bit is permitted to be cached in a TLB.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on the PE.
        WXN OFFSET(19) NUMBITS(1) [
            Disable = 0,
            Enable = 1,
        ],

        /// Traps EL0 execution of WFE instructions to EL1, from both Execution states.
        ///
        /// 0 Any attempt to execute a WFE instruction at EL0 is trapped to EL1, if the instruction
        ///   would otherwise have caused the PE to enter a low-power state.
        ///
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// In AArch32 state, the attempted execution of a conditional WFE instruction is only trapped if the
        /// instruction passes its condition code check.
        ///
        /// **Note:**
        ///
        /// Since a WFE or WFI can complete at any time, even without a Wakeup event, the traps on WFE of
        /// WFI are not guaranteed to be taken, even if the WFE or WFI is executed when there is no Wakeup
        /// event. The only guarantee is that if the instruction does not complete in finite time in the
        /// absence of a Wakeup event, the trap will be taken.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        NTWE OFFSET(18) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 executions of WFI instructions to EL1, from both execution states:
        ///
        /// 0 Any attempt to execute a WFI instruction at EL0 is trapped EL1, if the instruction would
        ///   otherwise have caused the PE to enter a low-power state.
        ///
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// In AArch32 state, the attempted execution of a conditional WFI instruction is only trapped if the
        /// instruction passes its condition code check.
        ///
        /// **Note:**
        ///
        /// Since a WFE or WFI can complete at any time, even without a Wakeup event, the traps on WFE of
        /// WFI are not guaranteed to be taken, even if the WFE or WFI is executed when there is no Wakeup
        /// event. The only guarantee is that if the instruction does not complete in finite time in the
        /// absence of a Wakeup event, the trap will be taken.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        NTWI OFFSET(16) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 accesses to the CTR_EL0 to EL1, from AArch64 state only.
        ///
        /// 0 Accesses to the CTR_EL0 from EL0 using AArch64 are trapped to EL1.
        ///
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        UCT OFFSET(15) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Traps EL0 execution of DC ZVA instructions to EL1, from AArch64 state only.
        ///
        /// 0 Any attempt to execute a DC ZVA instruction at EL0 using AArch64 is trapped to EL1.
        ///   Reading DCZID_EL0.DZP from EL0 returns 1, indicating that DC ZVA instructions
        ///   are not supported.
        ///
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        DZE OFFSET(14) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Instruction access Cacheability control, for accesses at EL0 and
        /// EL1:
        ///
        /// 0 All instruction access to Normal memory from EL0 and EL1 are Non-cacheable for all
        ///   levels of instruction and unified cache.
        ///
        ///   If the value of SCTLR_EL1.M is 0, instruction accesses from stage 1 of the EL1&0
        ///   translation regime are to Normal, Outer Shareable, Inner Non-cacheable, Outer
        ///   Non-cacheable memory.
        ///
        /// 1 This control has no effect on the Cacheability of instruction access to Normal memory
        ///   from EL0 and EL1.
        ///
        ///   If the value of SCTLR_EL1.M is 0, instruction accesses from stage 1 of the EL1&0
        ///   translation regime are to Normal, Outer Shareable, Inner Write-Through, Outer
        ///   Write-Through memory.
        ///
        /// When the value of the HCR_EL2.DC bit is 1, then instruction access to Normal memory from
        /// EL0 and EL1 are Cacheable regardless of the value of the SCTLR_EL1.I bit.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on the PE.
        ///
        /// When this register has an architecturally-defined reset value, this field resets to 0.
        I OFFSET(12) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// User Mask Access. Traps EL0 execution of MSR and MRS instructions that access the
        /// PSTATE.{D, A, I, F} masks to EL1, from AArch64 state only.
        ///
        /// 0 Any attempt at EL0 using AArch64 to execute an MRS , MSR(register) , or MSR(immediate)
        ///   instruction that accesses the [`DAIF`](module@super::super::DAIF) is trapped to EL1.
        ///
        /// 1 This control does not cause any instructions to be trapped.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on execution at EL0.
        UMA OFFSET(9) NUMBITS(1) [
            Trap = 0,
            DontTrap = 1,
        ],

        /// Non-aligned access. This bit controls generation of Alignment faults at EL1 and EL0 under certain conditions.
        ///
        /// LDAPR, LDAPRH, LDAPUR, LDAPURH, LDAPURSH, LDAPURSW, LDAR, LDARH, LDLAR, LDLARH,
        /// STLLR, STLLRH, STLR, STLRH, STLUR, and STLURH will or will not generate an Alignment
        /// fault if all bytes being accessed are not within a single 16-byte quantity,
        /// aligned to 16 bytes for accesses.
        NAA OFFSET(6) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// SP Alignment check enable for EL0.
        ///
        /// When set to 1, if a load or store instruction executed at EL0 uses the SP
        /// as the base address and the SP is not aligned to a 16-byte boundary,
        /// then a SP alignment fault exception is generated.
        SA0 OFFSET(4) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// SP Alignment check enable.
        ///
        /// When set to 1, if a load or store instruction executed at EL1 uses the SP
        /// as the base address and the SP is not aligned to a 16-byte boundary,
        /// then a SP alignment fault exception is generated.
        SA OFFSET(3) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Cacheability control, for data accesses.
        ///
        /// 0 All data access to Normal memory from EL0 and EL1, and all Normal memory accesses to
        ///   the EL1&0 stage 1 translation tables, are Non-cacheable for all levels of data and
        ///   unified cache.
        ///
        /// 1 This control has no effect on the Cacheability of:
        ///   - Data access to Normal memory from EL0 and EL1.
        ///   - Normal memory accesses to the EL1&0 stage 1 translation tables.
        ///
        /// When the value of the HCR_EL2.DC bit is 1, the PE ignores SCLTR.C. This means that
        /// Non-secure EL0 and Non-secure EL1 data accesses to Normal memory are Cacheable.
        ///
        /// When ARMv8.1-VHE is implemented, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on the PE.
        ///
        /// When this register has an architecturally-defined reset value, this field resets to 0.
        C OFFSET(2) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// Alignment check enable. This is the enable bit for Alignment fault checking at EL1 and EL0.
        ///
        /// Instructions that load or store one or more registers, other than load/store exclusive
        /// and load-acquire/store-release, will or will not check that the address being accessed
        /// is aligned to the size of the data element(s) being accessed depending on this flag.
        ///
        /// Load/store exclusive and load-acquire/store-release instructions have an alignment check
        /// regardless of the value of the A bit.
        A OFFSET(1) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// MMU enable for EL1 and EL0 stage 1 address translation. Possible values of this bit are:
        ///
        /// 0 EL1 and EL0 stage 1 address translation disabled.
        ///   - See the SCTLR_EL1.I field for the behavior of instruction accesses to Normal memory.
        ///
        /// 1 EL1 and EL0 stage 1 address translation enabled.
        M OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = SCTLR_EL1::Register;

    sys_coproc_read_raw!(u64, "SCTLR_EL1", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = SCTLR_EL1::Register;

    sys_coproc_write_raw!(u64, "SCTLR_EL1", "x");
}

pub const SCTLR_EL1: Reg = Reg {};
