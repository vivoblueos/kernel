// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2025 by the author(s)
//
// Author(s):
//   - Yan Tan <tanyan@kylinos.cn>

//! Extended Translation Control Register - EL1
//!
//! Provides control over the translation table walks for stage 1 of the EL1&0 translation regime.
//! This register is present only when FEAT_TCR2 is implemented and FEAT_AA64 is implemented.
//! Otherwise, direct accesses to TCR2_EL1 are UNDEFINED.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub TCR2_EL1 [
        // Reserved, RES0，[63:22]

        /// Force non-global for unassured translations using TTBR1_EL1.
        ///
        /// **When FEAT_THE is implemented:**
        ///
        /// This bit is permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        FNGNA1 OFFSET(21) NUMBITS(1) [],

        /// Force non-global for unassured translations using TTBR0_EL1
        ///
        /// **When FEAT_THE is implemented:**
        ///
        /// This bit is permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        FNGNA0 OFFSET(20) NUMBITS(1) [],

        // Reserved, RES0，[19]

        /// Force non-global translations for TTBR1_EL1.
        ///
        /// **When FEAT_ASID2 is implemented:**
        ///
        /// This bit is permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        FNG1 OFFSET(18) NUMBITS(1) [],


        /// Force non-global translations for TTBR0_EL1.
        ///
        /// **When FEAT_ASID2 is implemented:**
        ///
        /// This bit is permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        FNG0 OFFSET(17) NUMBITS(1) [],

        /// Enable use of two ASIDs.
        ///
        /// **When FEAT_ASID2 is implemented:**
        ///
        /// - 0 : Use of two ASIDs is disabled
        /// - 1 : Use of two ASIDs is enabled
        ///
        /// This bit is permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        A2 OFFSET(16) NUMBITS(1) [],

        /// Disable the Contiguous bit for the Start Table for TTBR1_EL1.
        ///
        /// **When FEAT_D128 is implemented and TCR2_EL1.D128 == 1:**
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        DisCH1 OFFSET(15) NUMBITS(1) [],

        /// Disable the Contiguous bit for the Start Table for TTBR0_EL1.
        ///
        /// **When FEAT_D128 is implemented and TCR2_EL1.D128 == 1:**
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        DisCH0 OFFSET(14) NUMBITS(1) [],

        // Reserved, RES0，[13:12]

        /// Hardware managed Access Flag for Table descriptors.
        ///
        /// **When FEAT_HAFT is implemented:**
        ///
        /// Controls whether hardware manages the Access Flag for Table descriptors.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        HAFT OFFSET(11) NUMBITS(1) [
            /// Hardware managed Access Flag for Table descriptors is disabled
            Disabled = 0,
            /// Hardware managed Access Flag for Table descriptors is enabled
            Enabled = 1
        ],

        /// Permit Translation table walk Incoherence.
        ///
        /// **When FEAT_THE is implemented:**
        ///
        /// Permits RCWS instructions to generate writes that have the Reduced Coherence property.
        ///
        /// This bit is permitted to be implemented as a read-only bit with a fixed value of 0.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        PTTWI OFFSET(10) NUMBITS(1) [],

        // Reserved, RES0，[9:6]

        /// Enables VMSAv9-128 translation system.
        ///
        /// **When FEAT_D128 is implemented:**
        ///
        /// - 0 : Translation system follows VMSAv8-64 translation process
        /// - 1 : Translation system follows VMSAv9-128 translation process
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        D128 OFFSET(5) NUMBITS(1) [],

        /// Enable Attribute Indexing Extension.
        ///
        /// **When FEAT_AIE is implemented:**
        ///
        /// This field is RES1 when TCR2_EL1.D128 is 1.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        AIE OFFSET(4) NUMBITS(1) [
            /// Attribute Indexing Extension Disabled
            Disabled = 0,
            /// Attribute Indexing Extension Enabled
            Enabled = 1
        ],

        /// Enables Permission Overlays for privileged accesses.
        ///
        /// **When FEAT_S1POE is implemented:**
        ///
        /// - 0 : Permission overlay disabled for EL1 access in stage 1 of EL1&0 translation regime.
        /// - 1 : Permission overlay enabled for EL1 access in stage 1 of EL1&0 translation regime.
        ///
        /// This bit is not permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        POE OFFSET(3) NUMBITS(1) [
            /// Permission overlay disabled for EL1 access
            Disabled = 0,
            /// Permission overlay enabled for EL1 access
            Enabled = 1
        ],

        /// Enables Permission Overlays for unprivileged accesses from EL1&0 translation regime.
        ///
        /// **When FEAT_S1POE is implemented:**
        ///
        /// - 0 : Permission overlay disabled for EL0 access in stage 1 of EL1&0 translation regime.
        /// - 1 : Permission overlay enabled for EL0 access in stage 1 of EL1&0 translation regime.
        ///
        /// This bit is not permitted to be cached in a TLB.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        E0POE OFFSET(2) NUMBITS(1) [
            /// Permission overlay disabled for EL0 access
            Disabled = 0,
            /// Permission overlay enabled for EL0 access
            Enabled = 1
        ],

        /// Enables usage of Indirect Permission Scheme.
        ///
        /// **When FEAT_S1PIE is implemented:**
        ///
        /// - 0 : Direct permission model
        /// - 1 : Indirect permission model
        ///
        /// This field is RES1 when TCR2_EL1.D128 is 1.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        PIE OFFSET(1) NUMBITS(1) [
            /// Direct permission model
            Direct = 0,
            /// Indirect permission model
            Indirect = 1
        ],

        /// Protected attribute enable.
        ///
        /// **When FEAT_THE is implemented:**
        ///
        /// Enables use of bit[52] of the stage 1 translation table entries as the Protected bit,
        /// for translations using TTBRn_EL1
        ///
        /// - 0 : For translations using TTBRn_EL1, bit[52] of each stage 1 translation table entry is not the Protected bit.
        /// - 1 : For translations using TTBRn_EL1, bit[52] of each stage 1 translation table entry is the Protected bit.
        ///
        /// If bit[52] is used as the Protected bit, it is not used as the Contiguous bit.
        ///
        /// This field is RES0 when TCR2_EL1.D128 is 1.
        ///
        /// This field is ignored by the PE and treated as zero when any of the following are true:
        /// - All of the following are true:
        ///   - EL2 is implemented and enabled in the current Security state.
        ///   - The Effective value of HCRX_EL2.TCR2En is 0.
        /// - EL3 is implemented and SCR_EL3.TCR2En == 0.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset:
        ///   - When the highest implemented Exception level is EL1, this field resets to '0'.
        ///   - Otherwise, this field resets to an architecturally UNKNOWN value.
        ///
        /// **Otherwise:**
        ///
        /// Reserved.
        PnCH OFFSET(0) NUMBITS(1) [
            /// bit[52] is not the Protected bit
            NotProtected = 0,
            /// bit[52] is the Protected bit
            Protected = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = TCR2_EL1::Register;

    sys_coproc_read_raw!(u64, "S3_0_C2_C0_3", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = TCR2_EL1::Register;

    sys_coproc_write_raw!(u64, "S3_0_C2_C0_3", "x");
}

pub const TCR2_EL1: Reg = Reg {};
