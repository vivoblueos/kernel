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

use tock_registers::{interfaces::Readable, register_bitfields};

// See: https://developer.arm.com/documentation/ddi0601/2024-12/AArch64-Registers//MPIDR-EL1--Multiprocessor-Affinity-Register
register_bitfields! [u64,
    /// Multiprocessor Affinity Register
    MPIDR_EL1 [
        /// Affinity level 3
        Aff3 OFFSET(32) NUMBITS(8) [],

        /// Reserved, RES1.
        RES1 OFFSET(31) NUMBITS(1) [],

        /// Indicates a single core system, as distinct from core 0 in a cluster.
        U OFFSET(30) NUMBITS(1) [
            MultiprocessorSystem = 0b0,
            UniprocessorSystem = 0b1,
        ],

        /// Indicates whether the lowest level of affinity consists of logical cores that are implemented using a multithreading type approach.
        MT OFFSET(24) NUMBITS(1) [],

        /// Affinity level 2.
        Aff2 OFFSET(16) NUMBITS(8) [],

        /// APart of Affinity level 1.
        Aff1 OFFSET(8) NUMBITS(8) [],

        /// Affinity level 0.
        Aff0 OFFSET(0) NUMBITS(8) []
    ]
];

pub struct MpidrEl1;

impl Readable for MpidrEl1 {
    type T = u64;
    type R = MPIDR_EL1::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let mpidr;
        unsafe {
            core::arch::asm!(
                "mrs {}, mpidr_el1",
                out(reg) mpidr,
                options(nomem, nostack, preserves_flags)
            );
        }
        mpidr
    }
}

pub const MPIDR_EL1: MpidrEl1 = MpidrEl1 {};
