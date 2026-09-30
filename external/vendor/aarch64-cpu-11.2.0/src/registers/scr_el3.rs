// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2019-2023 by the author(s)
//
// Author(s):
//   - Berkus Decker <berkus+github@metta.systems>

//! Secure Configuration Register - EL3, page D12.2.99 of armv8arm.
//! Defines the configuration of the current Security state. It specifies:
//! • The Security state of EL0, EL1, and EL2. The Security state is either Secure or Non-secure.
//! • The Execution state at lower Exception levels.
//! • Whether IRQ, FIQ, SError interrupts, and External abort exceptions are taken to EL3.
//! • Whether various operations are trapped to EL3.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub SCR_EL3 [
        /// Execution state control for lower Exception levels:
        ///
        /// 0 Lower levels are all AArch32.
        /// 1 The next lower level is AArch64.
        ///   If EL2 is present:
        ///     The Execution state for EL2 is AArch64.
        ///     EL2 controls EL1 and EL0 behaviors.
        ///   If EL2 is not present:
        ///     The Execution state for EL1 is AArch64.
        ///     The Execution state for EL0 is determined by the current value of PSTATE.nRW when
        ///     executing at EL0.
        ///
        /// If all lower Exception levels cannot use AArch32 then this bit is RAO/WI.
        ///
        /// When SCR_EL3.{EEL2,NS}=={1,0}, this bit is treated as 1 for all purposes other than
        /// reading or writing the register.
        ///
        /// The RW bit is permitted to be cached in a TLB.
        RW   OFFSET(10) NUMBITS(1) [
            AllLowerELsAreAarch32 = 0,
            NextELIsAarch64 = 1
        ],

        /// Hypervisor Call Enable
        ///
        /// 0 The HVC instruction is undefined at all exception levels.
        /// 1 The HVC instruction is enabled at EL1, EL2, or EL3.
        HCE OFFSET(8) NUMBITS(1) [
            HvcDisabled = 0,
            HvcEnabled = 1
        ],

        /// Secure Monitor call Disable
        ///
        /// 0 The SMC instruction is enabled at EL1, EL2, and EL3.
        ///
        /// 1 The SMC instruction is undefined at all exception levels. At EL1, in the Non-secure
        ///   state, the HCR_EL2.TSC bit has priority over this control.
        SMD OFFSET(7) NUMBITS(1) [
            SmcEnabled = 0,
            SmcDisabled = 1
        ],

        /// External Abort and SError interrupt routing.
        /// 0 When executing at Exception levels below EL3, External aborts and SError interrupts are not taken to EL3.
        ///     In addition, when executing at EL3:
        ///       SError interrupts are not taken.
        ///       External aborts are taken to EL3.
        ///
        /// 1 When executing at any Exception level, External aborts and SError interrupts are taken to EL3.
        EA  OFFSET(3) NUMBITS(1) [
            NotTaken = 0,
            Taken = 1
        ],

        /// Physical FIQ Routing.
        /// 0 When executing at Exception levels below EL3, physical FIQ interrupts are not taken
        ///   to EL3. When executing at EL3, physical FIQ interrupts are not taken.
        ///
        /// 1 When executing at any Exception level, physical FIQ interrupts are taken to EL3.
        FIQ OFFSET(2) NUMBITS(1) [
            NotTaken = 0,
            Taken = 1
        ],

        /// Physical IRQ Routing.
        /// 0 When executing at Exception levels below EL3, physical IRQ interrupts are not taken
        ///   to EL3. When executing at EL3, physical IRQ interrupts are not taken.
        ///
        /// 1 When executing at any Exception level, physical IRQ interrupts are taken to EL3.
        IRQ OFFSET(1) NUMBITS(1) [
            NotTaken = 0,
            Taken = 1
        ],

        /// Non-secure bit.
        /// 0 Indicates that EL0 and EL1 are in Secure state.
        ///
        /// 1 Indicates that Exception levels lower than EL3 are in Non-secure state, and so memory
        ///   accesses from those Exception levels cannot access Secure memory.
        ///
        /// When SCR_EL3.{EEL2, NS} == {1, 0}, then EL2 is using AArch64 and in Secure state.
        NS  OFFSET(0) NUMBITS(1) [
            Secure = 0,
            NonSecure = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = SCR_EL3::Register;

    sys_coproc_read_raw!(u64, "SCR_EL3", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = SCR_EL3::Register;

    sys_coproc_write_raw!(u64, "SCR_EL3", "x");
}

pub const SCR_EL3: Reg = Reg {};
