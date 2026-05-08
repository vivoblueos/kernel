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

use crate::arch::aarch64::registers::{
    mair_el2::MAIR_EL2, sctlr_el2::SCTLR_EL2, tcr_el2::TCR_EL2, ttbr0_el2::TTBR0_EL2,
};
use tock_registers::{interfaces::*, register_bitfields, registers::InMemoryRegister};

register_bitfields! {u64,
    pub PAGE_DESCRIPTOR_EL2 [
        XN      OFFSET(54) NUMBITS(1) [ False = 0, True = 1 ],
        OUTPUT_ADDR OFFSET(12) NUMBITS(36) [],
        AF      OFFSET(10) NUMBITS(1) [ False = 0, True = 1 ],
        SH      OFFSET(8)  NUMBITS(2) [
            NonShareable   = 0b00,
            OuterShareable = 0b10,
            InnerShareable = 0b11
        ],
        AP      OFFSET(6)  NUMBITS(2) [ RW = 0b00, RO = 0b10 ],
        ATTRINDX OFFSET(2) NUMBITS(3) [],
        TYPE    OFFSET(1)  NUMBITS(1) [ Block = 0, Table = 1 ],
        VALID   OFFSET(0)  NUMBITS(1) [ Invalid = 0, Valid = 1 ]
    ]
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct PageEntry(u64);

impl PageEntry {
    const fn new() -> Self {
        Self(0)
    }

    fn set(&mut self, output_addr: u64, device: bool) {
        let entry = InMemoryRegister::<u64, PAGE_DESCRIPTOR_EL2::Register>::new(0);
        let mut val = PAGE_DESCRIPTOR_EL2::VALID::Valid
            + PAGE_DESCRIPTOR_EL2::AF::True
            + PAGE_DESCRIPTOR_EL2::TYPE::Block;
        if device {
            val += PAGE_DESCRIPTOR_EL2::ATTRINDX.val(0) + PAGE_DESCRIPTOR_EL2::XN::True;
        } else {
            val += PAGE_DESCRIPTOR_EL2::ATTRINDX.val(1) + PAGE_DESCRIPTOR_EL2::SH::InnerShareable;
        }
        entry.write(val);
        self.0 = entry.get() | (output_addr & 0xFFFF_FFFF_C000_0000);
    }
}

#[used]
static mut EL2_PAGE_TABLE: El2PageTable = El2PageTable::new();

#[repr(C, align(4096))]
pub struct El2PageTable([PageEntry; 512]);

impl El2PageTable {
    const fn new() -> Self {
        El2PageTable([PageEntry::new(); 512])
    }
}

pub fn enable_el2_mmu() {
    unsafe {
        EL2_PAGE_TABLE.0[0].set(0x0, true); // 0~1G: Device
        EL2_PAGE_TABLE.0[1].set(0x4000_0000, false); // 1~2G: Normal
    }

    // MAIR_EL2: Attr0=Device nGnRE, Attr1=Normal WB
    MAIR_EL2.write(
        MAIR_EL2::Attr0_Device::NonGathering_NonReordering_EarlyWriteAck
            + MAIR_EL2::Attr1_Normal_Outer::WriteBack_NonTransient_ReadWriteAlloc
            + MAIR_EL2::Attr1_Normal_Inner::WriteBack_NonTransient_ReadWriteAlloc,
    );

    unsafe {
        let ttbr = &EL2_PAGE_TABLE as *const _ as u64;
        TTBR0_EL2.set(ttbr);
    }

    TCR_EL2.write(
        TCR_EL2::T0SZ.val(25)
            + TCR_EL2::TG0::KiB_4
            + TCR_EL2::SH0::Inner
            + TCR_EL2::ORGN0::WriteBack_ReadAlloc_NoWriteAlloc_Cacheable
            + TCR_EL2::IRGN0::WriteBack_ReadAlloc_NoWriteAlloc_Cacheable
            + TCR_EL2::PS::Bits_32,
    );

    unsafe {
        core::arch::asm!("dsb sy", options(nostack, nomem));
        core::arch::asm!("tlbi alle2", options(nostack, nomem));
        core::arch::asm!("dsb sy", options(nostack, nomem));
        core::arch::asm!("isb sy", options(nostack, nomem));
    }

    SCTLR_EL2.modify(SCTLR_EL2::M::Enable + SCTLR_EL2::C::Cacheable + SCTLR_EL2::I::Cacheable);
    unsafe {
        core::arch::asm!("isb sy", options(nostack, nomem));
    }
}
