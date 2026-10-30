// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2024 by the author(s)
//
// Author(s):
//   - Sangwan Kwon <sangwan.kwon@samsung.com>

//! Architectural Feature Trap Register - EL2
//!
//! Controls trapping to EL2 of accesses to CPACR, CPACR_EL1, trace, Activity Monitor, SME,
//! Streaming SVE, SVE, and Advanced SIMD and floating-point functionality.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CPTR_EL2 [
        /// Trap Activity Monitor access. Traps EL1 and EL0 accesses to all Activity Monitor
        /// registers to EL2.
        ///
        /// 0 Accesses from EL1 and EL0 to Activity Monitor registers are not trapped.
        ///
        /// 1 Accesses from EL1 and EL0 to Activity Monitor registers are trapped to EL2,
        /// when EL2 is enabled in the current Security state.
        TAM  OFFSET(30) NUMBITS(1) [],
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CPTR_EL2::Register;

    sys_coproc_read_raw!(u64, "CPTR_EL2", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CPTR_EL2::Register;

    sys_coproc_write_raw!(u64, "CPTR_EL2", "x");
}

pub const CPTR_EL2: Reg = Reg {};
