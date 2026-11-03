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

//! AArch64 MMU register setup and address-space activation.

use crate::mm::{paging::PageFormat, PhysicalAddress, VirtualAddress};
use aarch64_cpu::{
    asm::barrier::{dsb, isb, SY},
    registers::{MAIR_EL1, SCTLR_EL1, TCR_EL1, TTBR0_EL1, TTBR1_EL1},
};
use tock_registers::interfaces::*;

const KERNEL_VA_BITS: u64 = super::page::PageEntry::VIRT_ADDR_BITS as u64;
const TCR_TSZ: u64 = u64::BITS as u64 - KERNEL_VA_BITS;
pub(crate) const KERNEL_VIRT_START: u64 = crate::mm::KERNEL_VIRT_OFFSET as u64;
pub use crate::mm::{kernel_phys_to_virt, kernel_virt_to_phys};

#[inline]
fn flush_tlb_all() {
    super::asm::tlbi_all();
    dsb(SY);
    isb(SY);
}

/// Publish kernel page-table changes and retire translations on every CPU
/// in the inner-shareable domain before backing/table frames can be reused.
pub(crate) fn sync_kernel_mappings() {
    unsafe {
        core::arch::asm!(
            "dsb ishst",
            "tlbi vmalle1is",
            "dsb ish",
            "isb",
            options(nostack, preserves_flags),
        );
    }
}

pub fn init_el1_enable_mmu() {
    let phys_addr = unsafe { crate::mm::paging::init_boot_pgtable::<super::page::PageEntry>() };
    dsb(SY);
    TTBR0_EL1.set(phys_addr as u64);
    TTBR1_EL1.set(phys_addr as u64);

    // Keep slots 0..3 in sync with the attribute indices in arch::page.
    MAIR_EL1.write(
        MAIR_EL1::Attr1_Normal_Outer::WriteBack_NonTransient_ReadWriteAlloc
            + MAIR_EL1::Attr1_Normal_Inner::WriteBack_NonTransient_ReadWriteAlloc
            + MAIR_EL1::Attr0_Device::nonGathering_nonReordering_EarlyWriteAck
            + MAIR_EL1::Attr2_Normal_Outer::NonCacheable
            + MAIR_EL1::Attr2_Normal_Inner::NonCacheable
            + MAIR_EL1::Attr3_Normal_Outer::WriteThrough_NonTransient_ReadWriteAlloc
            + MAIR_EL1::Attr3_Normal_Inner::WriteThrough_NonTransient_ReadWriteAlloc,
    );
    // Configure address translation related control information.
    TCR_EL1.write(
        TCR_EL1::TBI0::Used
            + TCR_EL1::IPS::Bits_32
            + TCR_EL1::TG0::KiB_4
            + TCR_EL1::SH0::Inner
            + TCR_EL1::ORGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN0::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::EPD0::EnableTTBR0Walks
            + TCR_EL1::T0SZ.val(TCR_TSZ)
            + TCR_EL1::TG1::KiB_4
            + TCR_EL1::SH1::Inner
            + TCR_EL1::ORGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::EPD1::EnableTTBR1Walks
            + TCR_EL1::T1SZ.val(TCR_TSZ),
    );

    // Clear tlb.
    flush_tlb_all();
    // Enable the MMU.
    SCTLR_EL1.modify(
        SCTLR_EL1::M::Enable
            + SCTLR_EL1::C::Cacheable
            + SCTLR_EL1::I::Cacheable
            + SCTLR_EL1::SA::Enable,
    );
    isb(SY);
}

/// Install a completed kernel page table on this CPU.
///
/// # Safety
/// The root and all child tables must be valid for the configured format and
/// remain live. The new table must map the executing code, stack, data and
/// devices. Tables must be fully built and must not be concurrently modified.
pub unsafe fn activate_kernel_table(root: PhysicalAddress) {
    dsb(SY);
    TCR_EL1.modify(TCR_EL1::EPD0::DisableTTBR0Walks);
    TTBR0_EL1.set(0);
    TTBR1_EL1.set(root.into_raw() as u64);
    isb(SY);
    flush_tlb_all();
}
