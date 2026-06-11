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
    pub VTTBR_EL2 [
        /// VMID, bits [63:48] - Virtual Machine ID
        /// Used to tag ASID for Stage-2 translation
        VMID OFFSET(48) NUMBITS(16) [],

        /// BADDR, bits [47:1] - Translation Table Base Address
        /// Physical address of the Level-1 table for Stage-2 translation
        /// Must be aligned to table size (48-bit address space = 256KB aligned)
        BADDR OFFSET(1) NUMBITS(47) [],

        /// CnP, bit [0] - Common Not Private
        /// 0 = Not common, each PE uses separate tables
        /// 1 = Common, tables can be shared
        CnP OFFSET(0) NUMBITS(1) [
            NotCommon = 0,
            Common = 1
        ]
    ]
}

pub struct VttbrEl2;

impl Readable for VttbrEl2 {
    type T = u64;
    type R = VTTBR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, vttbr_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for VttbrEl2 {
    type T = u64;
    type R = VTTBR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr vttbr_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const VTTBR_EL2: VttbrEl2 = VttbrEl2 {};
