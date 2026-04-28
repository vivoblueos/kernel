// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

use tock_registers::{interfaces::*, register_bitfields};

register_bitfields! {u64,
    pub SPSR_EL2 [
        /// Debug exception mask. Controls routing of debug exceptions to EL2.
        D OFFSET(9) NUMBITS(1) [
            Allow = 0,
            Prohibit = 1
        ],

        /// SError interrupt mask.
        A OFFSET(8) NUMBITS(1) [
            Allow = 0,
            Prohibit = 1
        ],

        /// IRQ interrupt mask.
        I OFFSET(7) NUMBITS(1) [
            Allow = 0,
            Prohibit = 1
        ],

        /// FIQ interrupt mask.
        F OFFSET(6) NUMBITS(1) [
            Allow = 0,
            Prohibit = 1
        ],

        /// Exception mask bits. These bits mask PSTATE.A, I, F when taking an exception to EL2.
        /// The value saved is OR of the respective mask bits.
        E OFFSET(5) NUMBITS(1) [
            LittleEndian = 0,
            BigEndian = 1
        ],

        /// Instruction set state.
        /// 0: AArch64
        /// 1: AArch32
        IL OFFSET(4) NUMBITS(1) [
            Valid = 0,
            Illegal = 1
        ],

        /// Stack Pointer selection.
        /// 0: Use SP_EL0
        /// 1: Use SP_EL2
        SP OFFSET(0) NUMBITS(1) [
            EL0 = 0,
            EL2 = 1
        ],

        /// Mode/Execution state.
        M OFFSET(0) NUMBITS(4) [
            EL0t = 0b0000,
            EL1t = 0b0100,
            EL1h = 0b0101,
            EL2t = 0b1000,
            EL2h = 0b1001
        ]
    ]
}

pub struct SpsrEl2;

impl Readable for SpsrEl2 {
    type T = u64;
    type R = SPSR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, spsr_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for SpsrEl2 {
    type T = u64;
    type R = SPSR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr spsr_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const SPSR_EL2: SpsrEl2 = SpsrEl2 {};