// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub CNTP_CTL_EL0 [
        /// The status of the timer. This bit indicates whether the timer condition is met
        /// This bit is read-only.
        ISTATUS OFFSET(2) NUMBITS(1) [
            NotMet = 0,
            Met = 1
        ],

        /// Timer interrupt mask bit
        IMASK OFFSET(1) NUMBITS(1) [
            Unmasked = 0,
            Masked = 1
        ],

        /// Enables the timer
        ENABLE OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enabled = 1,
        ]
    ]
}

pub struct CntpCtlEl0;

impl Readable for CntpCtlEl0 {
    type T = u64;
    type R = CNTP_CTL_EL0::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, cntp_ctl_el0",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for CntpCtlEl0 {
    type T = u64;
    type R = CNTP_CTL_EL0::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr cntp_ctl_el0, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const CNTP_CTL_EL0: CntpCtlEl0 = CntpCtlEl0 {};
