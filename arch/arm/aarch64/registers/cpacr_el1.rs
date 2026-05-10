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

//See: https://developer.arm.com/documentation/ddi0601/latest/AArch64-Registers/CPACR-EL1--Architectural-Feature-Access-Control-Register
register_bitfields! {u64,
    pub CPACR_EL1 [
        //When FEAT_S1POE is implemented:
        // Enable access to POR_EL0.
        E0POE OFFSET(29) NUMBITS(1) [
            /// This control causes EL0 access to POR_EL0 to be trapped..
            Trap = 0b0,
            /// This control does not cause any instructions to be trapped.
            NoTrap = 0b1
        ],

        TTA OFFSET(28) NUMBITS(1) [
            /// This control does not cause any instructions to be trapped.
            NoTrap = 0b0,
            /// This control causes EL0 and EL1 System register accesses to all implemented trace registers to be trapped.
            Trap = 0b1
        ],

        SMEN OFFSET(24) NUMBITS(2) [
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl0El1 = 0b00,
            /// This control causes execution of these instructions at EL0 to be trapped,
            /// but does not cause execution of any instructions at EL1 to be trapped.
            TrapEl0 = 0b01,
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl1El0 = 0b10,
            /// This control does not cause execution of any instructions to be trapped.
            NoTrap = 0b11
        ],


        FPEN OFFSET(20) NUMBITS(2) [
            /// This control causes execution of these instructions at EL0 and EL1 to be trapped.
            TrapEl0El1 = 0b00,
            /// This control causes execution of these instructions at EL0 to be trapped, but
            /// does not cause any instructions at EL1 to be trapped.
            TrapEl0 = 0b01,
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl1El0 = 0b10,
            /// This control does not cause execution of any instructions to be trapped.
            NoTrap = 0b11
        ],

        ZEN OFFSET(16) NUMBITS(2) [
            /// This control causes execution of these instructions at EL0 and EL1 to be trapped.
            TrapEl0El1 = 0b00,
            /// This control causes execution of these instructions at EL0 to be trapped, but
            /// does not cause execution of any instructions at EL1 to be trapped.
            TrapEl0 = 0b01,
            /// This control causes execution of these instructions at EL1 and EL0 to be trapped.
            TrapEl1El0 = 0b10,
            /// This control does not cause execution of any instructions to be trapped.
            NoTrap = 0b11
        ]
    ]
}

pub struct CpacrEl1;

impl Readable for CpacrEl1 {
    type T = u64;
    type R = CPACR_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, cpacr_el1",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for CpacrEl1 {
    type T = u64;
    type R = CPACR_EL1::Register;
    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr cpacr_el1, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const CPACR_EL1: CpacrEl1 = CpacrEl1 {};
