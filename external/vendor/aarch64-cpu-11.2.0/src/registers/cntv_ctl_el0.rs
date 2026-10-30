// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>
//   - Gregor Reitzenstein <me@dequbed.space>

//! Counter-timer Virtual Timer Control register - EL0
//!
//! Control register for the virtual timer

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CNTV_CTL_EL0 [
        /// The status of the timer. This bit indicates whether the timer condition is met:
        ///
        /// 0 Timer condition is not met.
        /// 1 Timer condition is met.
        ///
        /// When the value of the ENABLE bit is 1, ISTATUS indicates whether the timer condition is
        /// met. ISTATUS takes no account of the value of the IMASK bit. If the value of ISTATUS is
        /// 1 and the value of IMASK is 0 then the timer interrupt is asserted.
        ///
        /// When the value of the ENABLE bit is 0, the ISTATUS field is UNKNOWN.
        ///
        /// This bit is read-only.
        ISTATUS OFFSET(2) NUMBITS(1) [],

        /// Timer interrupt mask bit. Permitted values are:
        ///
        /// 0 Timer interrupt is not masked by the IMASK bit.
        /// 1 Timer interrupt is masked by the IMASK bit.
        IMASK   OFFSET(1) NUMBITS(1) [],

        /// Enables the timer. Permitted values are:
        ///
        /// 0 Timer disabled.
        /// 1 Timer enabled.
        ///
        /// Setting this bit to 0 disables the timer output signal but the timer value accessible
        /// from `CNTV_TVAL_EL0` continues to count down.
        ///
        /// Disabling the output signal might be a power-saving option
        ENABLE  OFFSET(0) NUMBITS(1) []
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = CNTV_CTL_EL0::Register;

    sys_coproc_read_raw!(u64, "CNTV_CTL_EL0", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = CNTV_CTL_EL0::Register;

    sys_coproc_write_raw!(u64, "CNTV_CTL_EL0", "x");
}

pub const CNTV_CTL_EL0: Reg = Reg {};
