// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Interrupt Controller System Register Enable Register - EL2
//!
//! Controls whether the System register interface or the memory-mapped interface
//! to the GIC CPU interface is used for EL2.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub ICC_SRE_EL2 [
        /// Enables lower Exception level access to ICC_SRE_EL1.
        ///
        /// 0 When EL2 is implemented and enabled in the current Security state,
        ///   EL1 accesses to ICC_SRE_EL1 trap to EL2.
        ///
        /// 1 EL1 accesses to ICC_SRE_EL1 do not trap to EL2.
        ENABLE OFFSET(3) NUMBITS(1) [],

        /// Disable IRQ bypass.
        ///
        /// 0 IRQ bypass enabled.
        ///
        /// 1 IRQ bypass disabled.
        DIB    OFFSET(2) NUMBITS(1) [],

        /// Disable FIQ bypass.
        ///
        /// 0 FIQ bypass enabled.
        ///
        /// 1 FIQ bypass disabled.
        DFB    OFFSET(1) NUMBITS(1) [],

        /// System Register Enable.
        ///
        /// 0 The memory-mapped interface must be used. Access at EL2 to any ICH_* or
        /// ICC_* register other than ICC_SRE_EL1 or ICC_SRE_EL2, is trapped to EL2.
        ///
        /// 1 The System register interface to the ICH_* registers and the EL1 and EL2
        /// ICC_* registers is enabled for EL2.
        SRE    OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ICC_SRE_EL2::Register;

    sys_coproc_read_raw!(u64, "ICC_SRE_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ICC_SRE_EL2::Register;

    sys_coproc_write_raw!(u64, "ICC_SRE_EL2", "x");
}

pub const ICC_SRE_EL2: Reg = Reg {};
