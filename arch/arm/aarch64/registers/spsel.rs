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

use tock_registers::{interfaces::Writeable, register_bitfields};

// See: https://developer.arm.com/documentation/ddi0595/2020-12/AArch64-Registers/SPSel--Stack-Pointer-Select
register_bitfields! {u64,
    pub SPSEL [
        /// Stack pointer to use.
        SP OFFSET(0) NUMBITS(1) [
            EL0 = 0,
            ELx = 1
        ]
    ]
}

pub struct Spsel;

impl Writeable for Spsel {
    type T = u64;
    type R = SPSEL::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr spsel, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const SPSEL: Spsel = Spsel {};
