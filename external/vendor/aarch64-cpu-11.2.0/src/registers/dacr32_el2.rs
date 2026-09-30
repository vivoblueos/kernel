// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Valentin B. <valentin.be@protonmail.com>

//! Domain Access Control Register - EL2
//!
//! Allows access to the AArch32 DACR register from AArch64 state only. Its value
//! has no effect on execution in AArch64 state.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub DACR32_EL2 [
        /// Domain 15 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D15 OFFSET(30) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 14 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D14 OFFSET(28) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 13 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D13 OFFSET(26) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 12 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D12 OFFSET(24) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 11 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D11 OFFSET(22) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 10 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D10 OFFSET(20) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 9 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D9 OFFSET(18) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 8 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D8 OFFSET(16) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 7 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D7 OFFSET(14) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 6 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D6 OFFSET(12) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 5 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D5 OFFSET(10) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 4 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D4 OFFSET(8) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 3 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D3 OFFSET(6) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 2 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D2 OFFSET(4) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 1 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D1 OFFSET(2) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ],

        /// Domain 0 access permission.
        ///
        /// Values other than the pre-defined ones are reserved.
        ///
        /// NOTE: On Warm reset, this field resets to an undefined value.
        D0 OFFSET(0) NUMBITS(2) [
            /// No access. Any access to the domain generates a Domain fault.
            NoAccess = 0b00,
            /// Client access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Client = 0b01,
            /// Manager access. Accesses are not checked against the permission bits
            /// in the translation tables.
            Manager = 0b11
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = DACR32_EL2::Register;

    sys_coproc_read_raw!(u64, "DACR32_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = DACR32_EL2::Register;

    sys_coproc_write_raw!(u64, "DACR32_EL2", "x");
}

pub const DACR32_EL2: Reg = Reg;
