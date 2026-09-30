// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Bradley Landherr <landhb@users.noreply.github.com>

//! System Control Register - EL2
//!
//! Provides top level control of the system, including its memory system, at EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub SCTLR_EL2 [

        /// Exception endianness. The possible values are:
        ///
        /// 0  Little endian.
        /// 1  Big endian.
        EE OFFSET(25) NUMBITS(1) [
            Little = 0,
            Big = 1
        ],

        /// When FEAT_ExS is implemented control if taking an exception to EL2 is a context
        /// synchonizing event
        EIS OFFSET(22) NUMBITS(1) [
            IsNotSynch = 0,
            IsSynch = 1
        ],

        /// When FEAT_IESB is implemented control if an implict ESB is added at each exception
        /// and before each ERET to/from EL2
        IESB OFFSET(21) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Force treatment of all memory regions with write permissions as XN.
        /// The possible values are:
        ///
        /// 0  Regions with write permissions are not forced XN. This is the reset value.
        /// 1  Regions with write permissions are forced XN.
        WXN OFFSET(19) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Instruction Cache Control, two possible values:
        ///
        /// 0 All instruction access to Normal memory from EL2 are Non-cacheable for all
        ///   levels of instruction and unified cache.
        ///
        ///   If the value of SCTLR_EL2.M is 0, instruction accesses from stage 1 of the EL2 or EL2&0
        ///   translation regime are to Normal, Outer Shareable, Inner Non-cacheable, Outer
        ///   Non-cacheable memory.
        ///
        /// 1 This control has no effect on the Cacheability of instruction access to Normal memory
        ///   from EL2 and, when EL2 is enabled in the current Security state and
        ///   HCR_EL2.{E2H, TGE} == {1, 1}, instruction access to Normal memory from EL0.
        ///
        ///   If the value of SCTLR_EL2.M is 0, instruction accesses from stage 1 of the EL2&0
        ///   translation regime are to Normal, Outer Shareable, Inner Write-Through, Outer
        ///   Write-Through memory.
        ///
        /// When EL2 is disabled, and the value of HCR_EL2.{E2H, TGE} is {1, 1}, this bit
        /// has no effect on the PE.
        ///
        /// On a Warm reset, in a system where the PE resets into EL2, this field resets to 0.
        I OFFSET(12) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// When FEAT_ExS is implemented Exception exit is a context synchronization event.
        EOS OFFSET(11) NUMBITS(1) [
            IsNotSynch = 0,
            IsSynch = 1
        ],

        /// SP Alignment check enable.
        ///
        /// When set to 1, if a load or store instruction executed at EL2 uses the SP
        /// as the base address and the SP is not aligned to a 16-byte boundary,
        /// then a SP alignment fault exception is generated.
        SA OFFSET(3) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Cacheability control, for data accesses.
        ///
        /// 0 The following are Non-cacheable for all levels of data and unified cache:
        ///   - Data accesses to Normal memory from EL2.
        ///   - When HCR_EL2.{E2H, TGE} != {1, 1}, Normal memory accesses to the EL2 translation tables.
        ///   - When EL2 is enabled in the current Security state and HCR_EL2.{E2H, TGE} == {1, 1}:
        ///     - Data accesses to Normal memory from EL0.
        ///     - Normal memory accesses to the EL2&0 translation tables.
        ///
        /// 1 This control has no effect on the Cacheability of:
        ///   - Data access to Normal memory from EL2.
        ///   - When HCR_EL2.{E2H, TGE} != {1, 1}, Normal memory accesses to the EL2 translation tables.
        ///   - When EL2 is enabled in the current Security state and HCR_EL2.{E2H, TGE} == {1, 1}:
        ///     - Data accesses to Normal memory from EL0.
        ///     - Normal memory accesses to the EL2&0 translation tables.
        ///
        /// When EL2 is disabled in the current Security state or HCR_EL2.{E2H, TGE} != {1, 1},
        /// this bit has no effect on the EL1&0 translation regime.
        ///
        /// On a Warm reset, in a system where the PE resets into EL2, this field resets to 0.
        C OFFSET(2) NUMBITS(1) [
            NonCacheable = 0,
            Cacheable = 1
        ],

        /// Alignment check enable. This is the enable bit for Alignment fault checking at EL2 and,
        /// when EL2 is enabled in the current Security state and HCR_EL2.{E2H, TGE} == {1, 1}, EL0.
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

        /// MMU enable for EL2 or EL2&0 stage 1 address translation. Possible values of this bit are:
        ///
        /// 0 - When HCR_EL2.{E2H, TGE} != {1, 1}, EL2 stage 1 address translation disabled.
        ///   - When HCR_EL2.{E2H, TGE} == {1, 1}, EL2&0 stage 1 address translation disabled.
        ///   - See the SCTLR_EL2.I field for the behavior of instruction accesses to Normal memory.
        ///
        /// 1 - When HCR_EL2.{E2H, TGE} != {1, 1}, EL2 stage 1 address translation enabled.
        ///   - When HCR_EL2.{E2H, TGE} == {1, 1}, EL2&0 stage 1 address translation enabled.
        ///
        /// On a Warm reset, in a system where the PE resets into EL2, this field resets to 0.
        M OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = SCTLR_EL2::Register;

    sys_coproc_read_raw!(u64, "SCTLR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = SCTLR_EL2::Register;

    sys_coproc_write_raw!(u64, "SCTLR_EL2", "x");
}

pub const SCTLR_EL2: Reg = Reg {};
