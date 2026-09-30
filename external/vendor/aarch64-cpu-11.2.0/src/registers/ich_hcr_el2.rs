// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Interrupt Controller Hyp Control Register - EL2
//!
//! Controls the environment for VMs.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub ICH_HCR_EL2 [
        /// This field is incremented whenever a successful write to a virtual EOIR or
        /// DIR register would have resulted in a virtual interrupt deactivation.
        EOIcount OFFSET(27) NUMBITS(5) [],

        /// When ICH_VTR_EL2.DVIM == 1:
        /// Directly-injected Virtual Interrupt Mask.
        DVIM OFFSET(15) NUMBITS(1) [],

        /// When FEAT_GICv3_TDIR is implemented:
        /// Trap EL1 writes to ICC_DIR_EL1 and ICV_DIR_EL1.
        TDIR OFFSET(14) NUMBITS(1) [],

        /// When FEAT_GICv4p1 is implemented:
        /// Controls whether deactivation of virtual SGIs can increment ICH_HCR_EL2.EOIcount.
        vSGIEOICount OFFSET(8) NUMBITS(1) [],

        /// VM Group 1 Disabled Interrupt Enable. Enables the signaling of a maintenance interrupt
        /// while signaling of Group 1 interrupts from the virtual CPU interface to the connected
        /// vPE is disabled.
        VGrp1DIE OFFSET(7) NUMBITS(1) [],

        /// VM Group 1 Enabled Interrupt Enable. Enables the signaling of a maintenance interrupt
        /// while signaling of Group 1 interrupts from the virtual CPU interface to the connected
        /// vPE is enabled
        VGrp1EIE OFFSET(6) NUMBITS(1) [],

        /// VM Group 0 Disabled Interrupt Enable. Enables the signaling of a maintenance interrupt
        /// while signaling of Group 0 interrupts from the virtual CPU interface to the connected
        /// vPE is disabled.
        VGrp0DIE OFFSET(5) NUMBITS(1) [],

        /// VM Group 0 Enabled Interrupt Enable. Enables the signaling of a maintenance interrupt
        /// while signaling of Group 0 interrupts from the virtual CPU interface to the connected
        /// vPE is enabled
        VGrp0EIE OFFSET(4) NUMBITS(1) [],

        /// No Pending Interrupt Enable. Enables the signaling of a maintenance interrupt when
        /// there are no List registers with the State field set to 0b01 (pending).
        NPIE OFFSET(3) NUMBITS(1) [],

        /// List Register Entry Not Present Interrupt Enable. Enables the signaling of a maintenance
        /// interrupt while the virtual CPU interface does not have a corresponding valid List
        /// register entry for an EOI request.
        LRENPIE OFFSET(2) NUMBITS(1) [],

        /// Underflow Interrupt Enable. Enables the signaling of a maintenance interrupt when the
        /// List registers are empty, or hold only one valid entry.
        UIE OFFSET(1) NUMBITS(1) [],

        /// Enable. Global enable bit for the virtual CPU interface.
        En OFFSET(0) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ICH_HCR_EL2::Register;

    sys_coproc_read_raw!(u64, "ICH_HCR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ICH_HCR_EL2::Register;

    sys_coproc_write_raw!(u64, "ICH_HCR_EL2", "x");
}

pub const ICH_HCR_EL2: Reg = Reg {};
