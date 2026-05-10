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

use super::{
    asm,
    asm::DsbOptions,
    registers::{mair_el1::*, sctlr_el1::*, tcr_el1::*, ttbr0_el1::TTBR0_EL1},
};
use core::sync::atomic::{AtomicBool, Ordering};
use tock_registers::{interfaces::*, register_bitfields, registers::InMemoryRegister};

#[repr(u64)]
#[derive(Debug, Clone, Copy)]
pub enum MemAttributes {
    Device = 0,
    Normal = 1,
}

register_bitfields! {u64,
    pub PAGE_DESCRIPTOR [
        /// Unprivileged execute-never.
        UXN OFFSET(54) NUMBITS(1) [
            False = 0,
            True = 1
        ],

        /// Privileged execute-never.
        PXN OFFSET(53) NUMBITS(1) [
            False = 0,
            True = 1
        ],

        /// Current page table entry is in a continuous set of physical pages
        CONT_PHY_PAGES OFFSET(52) NUMBITS(1) [],

        /// Indicates that the page has been modified
        DMB OFFSET(51) NUMBITS(1) [],

        /// Output physical address
        OUTPUT_ADDR OFFSET(16) NUMBITS(36) [],

        /// When this bit is set, it means that the TLB page table entry corresponding to this page is process-specific.
        NG OFFSET(11) NUMBITS(1) [
            False = 0,
            True = 1
        ],

        /// Access flag, The hardware will automatically set up when you visit the page for the first time
        AF OFFSET(10) NUMBITS(1) [
            False = 0,
            True = 1
        ],

        /// Shared Memory Attributes
        SH OFFSET(8) NUMBITS(2) [
            NotShareable = 0b00,
            OuterShareable = 0b10,
            InnerShareable = 0b11
        ],

        /// Date access Permissions.
        /// AP[1] :
        ///   0: not accessible via EL0, but accessible via EL1
        ///   1: accessed through EL0 and higher privilege exceptions
        /// AP[2] :
        ///   0: read only
        ///   1: read and write
        AP OFFSET(6) NUMBITS(2) [
            EL1_RW = 0b00,
            EL0_RW = 0b01,
            EL1_RO = 0b10,
            EL0_RO = 0b11
        ],

        /// Non-secure
        NS OFFSET(5) NUMBITS(1) [],

        /// Memory attributes index.
        ATTRINDX OFFSET(2) NUMBITS(3) [],

        /// 0: Reserved page table entries
        /// 1: Page table
        TYPE OFFSET(1) NUMBITS(1) [
            Reserved = 0,
            Page = 1
        ],

        /// 0: Invalid descriptor
        /// 1: valid descriptor
        VALID OFFSET(0) NUMBITS(1) [
            Invalid = 0,
            Valid = 1
        ]
    ]
}

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct PageEntry(u64);

impl PageEntry {
    // Create a new invalid entry
    const fn new() -> Self {
        Self(0)
    }

    pub const fn from_u64(value: u64) -> Self {
        Self(value)
    }

    // Set page entry
    fn set(&mut self, output_addr: u64, attributes: MemAttributes) -> Result<(), &'static str> {
        if self.is_valid() {
            return Err("page entry is set");
        }
        let entry = InMemoryRegister::<u64, PAGE_DESCRIPTOR::Register>::new(0);
        match attributes {
            MemAttributes::Device => entry.write(
                PAGE_DESCRIPTOR::VALID::Valid
                    + PAGE_DESCRIPTOR::AF::True
                    + PAGE_DESCRIPTOR::ATTRINDX.val(MemAttributes::Device as u64)
                    + PAGE_DESCRIPTOR::UXN::True,
            ),
            MemAttributes::Normal => entry.write(
                PAGE_DESCRIPTOR::VALID::Valid
                    + PAGE_DESCRIPTOR::AF::True
                    + PAGE_DESCRIPTOR::ATTRINDX.val(MemAttributes::Normal as u64)
                    + PAGE_DESCRIPTOR::SH::InnerShareable
                    + PAGE_DESCRIPTOR::NG::True,
            ),
        }
        self.0 = entry.get() | output_addr;
        Ok(())
    }

    // Check the entry is valid
    fn is_valid(&self) -> bool {
        InMemoryRegister::<u64, PAGE_DESCRIPTOR::Register>::new(self.0)
            .is_set(PAGE_DESCRIPTOR::VALID)
    }
}

// This page table must be available before `init_runtime()` clears `.bss`,
// because we may set up EL1 MMU state while still running in EL2.
#[used]
#[link_section = ".data"]
static mut TABLE_MANAGER: PageTableManager = PageTableManager::new();

#[repr(C, align(4096))]
pub struct PageTableManager([PageEntry; 512]);

impl PageTableManager {
    const fn new() -> Self {
        PageTableManager([PageEntry::new(); 512])
    }

    fn init(normal_l1_bases: &[u64], device_l1_bases: &[u64]) {
        let table = unsafe { &mut TABLE_MANAGER };
        // Preserve the old kernel-side policy that device mappings win if a
        // board accidentally supplies overlapping L1 bases: PageEntry::set()
        // ignores later attempts to write an already-valid entry.
        for &base in device_l1_bases {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set(base, MemAttributes::Device);
        }
        for &base in normal_l1_bases {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set(base, MemAttributes::Normal);
        }
    }
}

// Indicate whether the page table initialization is done.
static PAGETABLE_INIT_DONE: AtomicBool = AtomicBool::new(false);

pub fn enable_mmu(cpu_id: usize, normal_l1_bases: &[u64], device_l1_bases: &[u64]) {
    // Only allow CPU0 to initialize the page table, other cores wait. The
    // board-owned L1 mapping policy is passed in by the kernel facade so this
    // arch crate does not depend on kernel boards.
    if cpu_id == 0 {
        PageTableManager::init(normal_l1_bases, device_l1_bases);
        PAGETABLE_INIT_DONE.store(true, Ordering::Release);
        // Wake up all cores waiting on wfe
        unsafe {
            core::arch::asm!("sev", options(nostack, nomem));
        }
    } else {
        // Wait for CPU0 to finish page table initialization.
        while !PAGETABLE_INIT_DONE.load(Ordering::Acquire) {
            unsafe {
                core::arch::asm!("wfe", options(nostack, nomem));
            }
        }
    }
    // Set physical table base addr.
    unsafe {
        core::arch::asm!(
            "adrp {temp}, {tbl}",
            "msr ttbr0_el1, {temp}",
            temp = out(reg) _,
            tbl = sym TABLE_MANAGER,
            options(nostack, nomem)
        )
    };
    // Set memory type.
    MAIR_EL1.write(
        MAIR_EL1::Attr1_Normal_Outer::WriteBack_NonTransient_ReadWriteAlloc
            + MAIR_EL1::Attr1_Normal_Inner::WriteBack_NonTransient_ReadWriteAlloc
            + MAIR_EL1::Attr0_Device::NonGathering_NonReordering_EarlyWriteAck,
    );
    // Configure address translation related control information.
    TCR_EL1.write(
        TCR_EL1::TBI0::Used
            + TCR_EL1::IPS::Bits_32
            + TCR_EL1::TG0::KiB_4
            + TCR_EL1::SH0::InnerShareable
            + TCR_EL1::ORGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::EPD1::DisableTTBR1Walks
            + TCR_EL1::EPD0::EnableTTBR0Walks
            + TCR_EL1::T0SZ.val(25),
    );
    // Clear tlb.
    asm::tlbi_all();
    asm::dsb(DsbOptions::Sys);
    asm::isb_sy();
    // Enable the MMU.
    SCTLR_EL1.modify(
        SCTLR_EL1::M::Enable
            + SCTLR_EL1::C::Cacheable
            + SCTLR_EL1::I::Cacheable
            + SCTLR_EL1::SA::Enable,
    );
    asm::isb_sy();
}
