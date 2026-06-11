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

        /// PTW, bit [2] - Page Table Walk
        PTW OFFSET(2) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// FMO, bit [3] - Asynchronous Memory Abort Override
        FMO OFFSET(3) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// IMO, bit [4] - IRQ Mask Override
        IMO OFFSET(4) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// AMO, bit [5] - Asynchronous Abort Routing
        AMO OFFSET(5) NUMBITS(1) [
            EL1Handled = 0,
            EL2Handled = 1
        ],

        /// VF, bit [6] - Virtual FIQ
        VF OFFSET(6) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// VI, bit [7] - Virtual IRQ
        VI OFFSET(7) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// VSE, bit [8] - Virtual System Error
        VSE OFFSET(8) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// FB, bit [9] - Force Broadcast
        FB OFFSET(9) NUMBITS(1) [
            Normal = 0,
            ForceBroadcast = 1
        ],

        /// BSU, bits [11:10] - Barrier Shareability Upgrade
        BSU OFFSET(10) NUMBITS(2) [
            NoEffect = 0b00,
            InnerShareable = 0b01,
            OuterShareable = 0b10,
            FullShareable = 0b11
        ],

        /// DC, bit [12] - Default Cacheable
        DC OFFSET(12) NUMBITS(1) [
            Disable = 0,
            Enable = 1
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

        /// TSC, bit [19] - TRAP SMC instruction
        TSC OFFSET(19) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TACR, bit [21] - Trap ACTLR accesses
        TACR OFFSET(21) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TSW, bit [22] - Trap Data Cache instructions by Set/Way
        TSW OFFSET(22) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TPCP, bit [23] - Trap Cache Maintenance instructions
        TPCP OFFSET(23) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TVM, bit [26] - Trap Virtual Memory Controls
        TVM OFFSET(26) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// TGE, bit [27] - Trap General Exceptions
        TGE OFFSET(27) NUMBITS(1) [
            GuestMode = 0,
            HostMode = 1
        ],

        /// TDZ, bit [28] - Trap DC ZVA instruction
        TDZ OFFSET(28) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// HCD, bit [29] - HVC Instruction Disable
        HCD OFFSET(29) NUMBITS(1) [
            EnableHVC = 0,
            DisableHVC = 1
        ],

        /// TRVM, bit [30] - Trap Reads of Virtual Memory Controls
        TRVM OFFSET(30) NUMBITS(1) [
            NoTrap = 0,
            Trap = 1
        ],

        /// RW, bit [31] - Register width control
        /// 0 = EL1 is AArch32
        /// 1 = EL1 is AArch64
        RW OFFSET(31) NUMBITS(1) [
            EL1AArch32 = 0,
            EL1AArch64 = 1
        ],

        /// CD, bit [32] - Disable Stage 2 Data Cache
        CD OFFSET(32) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],

        /// ID, bit [33] - Disable Stage 2 Instruction Cache
        ID OFFSET(33) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],

        /// E2H, bit [34] - EL2 Host
        E2H OFFSET(34) NUMBITS(1) [
            Disable = 0,
            Enable = 1
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
