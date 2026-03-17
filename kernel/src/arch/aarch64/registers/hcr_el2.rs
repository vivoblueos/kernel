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
    pub HCR_EL2 [
        /// VM, bit [0] - Virtualization Enable
        VM OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// SWIO, bit [1] - Set/Way Invalidate Override
        SWIO OFFSET(1) NUMBITS(1) [
            Invalidate = 0,
            Set = 1
        ],

        /// FWB, bit [2] - Force Write-back
        FWB OFFSET(2) NUMBITS(1) [
            Normal = 0,
            ForceWB = 1
        ],

        /// AMO, bit [3] - Asynchronous Memory Abort Override
        AMO OFFSET(3) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// IMO, bit [4] - IRQ Mask Override
        IMO OFFSET(4) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// FMO, bit [5] - FIQ Mask Override
        FMO OFFSET(5) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// TGE, bit [6] - Trap General Exceptions
        TGE OFFSET(6) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TWI, bit [13] - Trap WFI
        /// 0 = WFI not trapped
        /// 1 = WFI trapped to EL2
        TWI OFFSET(13) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TWE, bit [14] - Trap WFE
        TWE OFFSET(14) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// DCVA, bit [15] - Data Cache Zero By VA
        DCVA OFFSET(15) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// AT, bit [16] - Address Translation
        AT OFFSET(16) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// ST, bit [17] - Store Team Register
        ST OFFSET(17) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// VSE, bit [18] - Virtual System Error
        VSE OFFSET(18) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// VI, bit [19] - Virtual IRQ
        VI OFFSET(19) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// VF, bit [20] - Virtual FIQ
        VF OFFSET(20) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// FMO, bit [21] - Cache Maintenance Override
        FMO_CM OFFSET(21) NUMBITS(1) [
            Normal = 0,
            Override = 1
        ],

        /// AMO_BIT, bit [22] - AMO for instruction
        AMO_BIT OFFSET(22) NUMBITS(1) [
            Normal = 0,
            Override = 1
        ],

        /// RW, bit [31] - Register width control
        /// 0 = EL1 is AArch32
        /// 1 = EL1 is AArch64
        RW OFFSET(31) NUMBITS(1) [
            EL1AArch32 = 0,
            EL1AArch64 = 1
        ],

        /// PTW, bit [23] - Page Table Walk
        PTW OFFSET(23) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],

        /// HCD, bit [24] - Hypervisor Call Disable
        HCD OFFSET(24) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],

        /// TDZ, bit [25] - TRAP DC ZVA
        TDZ OFFSET(25) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TSC, bit [31] - TRAP SC
        TSC OFFSET(31) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TACR, bit [33] - TRAP ACTLR
        TACR OFFSET(33) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TIDCP, bit [36] - TRAP IMPLEMENTATION DEFINED
        TIDCP OFFSET(36) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TOCU, bit [38] - TRAP OSLAR
        TOCU OFFSET(38) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TID4, bit [40] - TRAP ID bits
        TID4 OFFSET(40) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ]
    ]
}

pub struct HcrEl2;

impl Readable for HcrEl2 {
    type T = u64;
    type R = HCR_EL2::Register;

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, hcr_el2",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for HcrEl2 {
    type T = u64;
    type R = HCR_EL2::Register;

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr hcr_el2, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const HCR_EL2: HcrEl2 = HcrEl2 {};
