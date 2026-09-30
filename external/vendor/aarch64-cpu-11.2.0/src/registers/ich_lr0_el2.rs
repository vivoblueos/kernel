// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Interrupt Controller List Registers - EL2
//!
//! Provides interrupt context information for the virtual CPU interface.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub ICH_LR0_EL2 [
        /// The state of the interrupt.
        State OFFSET(62) NUMBITS(2) [
            Invalid = 0b00,
            Pending = 0b01,
            Active = 0b10,
            PendingAndActive = 0b11,
        ],

        /// Indicates whether this virtual interrupt maps directly to a hardware interrupt, meaning
        /// that it corresponds to a physical interrupt. Deactivation of the virtual interrupt also
        /// causes the deactivation of the physical interrupt with the ID that the pINTID field
        /// indicates.
        HW OFFSET(61) NUMBITS(1) [],

        /// Indicates the group for this virtual interrupt.
        Group OFFSET(60) NUMBITS(1) [],

        /// When FEAT_GICv3_NMI is implemented:
        /// Indicates whether the virtual priority has the non-maskable property.
        NMI OFFSET(59) NUMBITS(1) [],

        /// The priority of this interrupt.
        Priority OFFSET(48) NUMBITS(8) [],

        /// Physical INTID, for hardware interrupts.
        pINTID OFFSET(32) NUMBITS(13) [],

        /// If this bit is 1, then when the interrupt identified by vINTID is deactivated,
        /// a maintenance interrupt is asserted.
        EOI OFFSET(41) NUMBITS(1) [],

        /// Virtual INTID of the interrupt.
        vINTID OFFSET(0) NUMBITS(32) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_read_raw!(u64, "ICH_LR0_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = ();

    sys_coproc_write_raw!(u64, "ICH_LR0_EL2", "x");
}

pub const ICH_LR0_EL2: Reg = Reg {};
