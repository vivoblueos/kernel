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

// ============================================================================
// Linear Mapping Layout (AArch64 EL1)
// ============================================================================
//
// KERNEL_VA_BITS = 39   →  512 GB virtual address space
// LINEAR_OFFSET  = 0xFFFF_FF80_0000_0000  (u64::MAX << 39)
//
//   Virtual Address Space (TTBR1, 39-bit)
//   ┌─────────────────────────────────────────────────────────┐ 0xFFFF_FFFF_FFFF_FFFF
//   │                                                         │
//   │  ┌─────────────────────────────────────────────────────┐│ 0xFFFF_FFFF_0000_0000 + 4 GB
//   │  │  Linear-mapped DRAM (4 × 1 GB L1 blocks)           ││
//   │  │  PA 0x0000_0000_0000 → VA 0xFFFF_FF80_0000_0000    ││
//   │  │  PA 0x0000_4000_0000 → VA 0xFFFF_FF80_4000_0000    ││
//   │  │  PA 0x0000_8000_0000 → VA 0xFFFF_FF80_8000_0000    ││
//   │  │  PA 0x0000_C000_0000 → VA 0xFFFF_FF80_C000_0000    ││
//   │  └─────────────────────────────────────────────────────┘│ 0xFFFF_FF80_0000_0000 ← KERNEL_VIRT_START
//   │                                                         │
//   │  (unmapped)                                             │
//   │                                                         │
//   └─────────────────────────────────────────────────────────┘ 0xFFFF_FF80_0000_0000
//
//   Translation:
//     VA = PA + LINEAR_OFFSET   (kernel_phys_to_virt)
//     PA = VA - LINEAR_OFFSET   (kernel_virt_to_phys)
//
// ============================================================================

use crate::arch::aarch64::{
    asm,
    asm::DsbOptions,
    registers::{
        mair_el1::*, sctlr_el1::*, tcr_el1::*, ttbr0_el1::TTBR0_EL1, ttbr1_el1::TTBR1_EL1,
    },
};
use core::{
    mem, ptr,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};
use tock_registers::{interfaces::*, register_bitfields, registers::InMemoryRegister};

const L1_BLOCK_SIZE: u64 = 1 << 30;
const PAGE_SIZE: usize = 4096;
const PAGE_MASK: usize = PAGE_SIZE - 1;
const PAGE_TABLE_INDEX_MASK: usize = 0x1ff;
const L1_SHIFT: usize = 30;
const L2_SHIFT: usize = 21;
const L3_SHIFT: usize = 12;
const PAGE_DESCRIPTOR_ADDR_MASK: u64 = 0x0000_ffff_ffff_f000;
const KERNEL_VA_BITS: u64 = 39;
const TCR_TSZ: u64 = u64::BITS as u64 - KERNEL_VA_BITS;
pub(crate) const KERNEL_VIRT_START: u64 = crate::mm::KERNEL_VIRT_OFFSET as u64;

pub use crate::mm::{kernel_phys_to_virt, kernel_virt_to_phys};

// End of the kernel-reserved virtual address range, including the heap.
extern "C" {
    static mut _end: u8;
}

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

#[derive(Copy, Clone)]
enum DescriptorKind {
    Block,
    Page,
}

impl PageEntry {
    // Create a new invalid entry
    const fn new() -> Self {
        Self(0)
    }

    pub const fn from_u64(value: u64) -> Self {
        Self(value)
    }

    fn set_descriptor(
        &mut self,
        output_addr: u64,
        attributes: MemAttributes,
        descriptor_kind: DescriptorKind,
    ) -> Result<(), &'static str> {
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

        let mut value = entry.get();
        match descriptor_kind {
            DescriptorKind::Block => {
                value |= output_addr;
            }
            DescriptorKind::Page => {
                value |= PAGE_DESCRIPTOR::TYPE::Page.value;
                value |= output_addr & PAGE_DESCRIPTOR_ADDR_MASK;
            }
        }

        self.0 = value;
        Ok(())
    }

    fn set_block(
        &mut self,
        output_addr: u64,
        attributes: MemAttributes,
    ) -> Result<(), &'static str> {
        self.set_descriptor(output_addr, attributes, DescriptorKind::Block)
    }

    fn set_page(
        &mut self,
        output_addr: u64,
        attributes: MemAttributes,
    ) -> Result<(), &'static str> {
        self.set_descriptor(output_addr, attributes, DescriptorKind::Page)
    }

    /// Set a page descriptor with explicit AP (access permissions).
    ///
    /// This is the same as `set_page` but allows the caller to override
    /// the AP field (e.g. `PAGE_DESCRIPTOR::AP::EL0_RW` for user-space
    /// accessible pages).  The caller provides the AP value to OR into
    /// the descriptor after the standard attribute setup.
    fn set_page_with_ap(
        &mut self,
        output_addr: u64,
        attributes: MemAttributes,
        ap: u64,
    ) -> Result<(), &'static str> {
        // Build base descriptor the same way as set_descriptor.
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
        // Apply the caller-supplied AP bits.
        // ap is already a pre-shifted FieldValue (.value), so no extra shift.
        let mut value = entry.get() | ap;
        value |= PAGE_DESCRIPTOR::TYPE::Page.value;
        value |= output_addr & PAGE_DESCRIPTOR_ADDR_MASK;
        self.0 = value;
        Ok(())
    }

    fn set_table(&mut self, table: *mut PageTableManager) -> Result<(), &'static str> {
        if self.is_valid() {
            return Err("page entry is set");
        }
        let table_phys = kernel_virt_to_phys(table as usize) as u64;
        let entry = InMemoryRegister::<u64, PAGE_DESCRIPTOR::Register>::new(0);
        entry.write(PAGE_DESCRIPTOR::VALID::Valid + PAGE_DESCRIPTOR::TYPE::Page);
        self.0 = entry.get() | (table_phys & PAGE_DESCRIPTOR_ADDR_MASK);
        Ok(())
    }

    // Check the entry is valid
    fn is_valid(&self) -> bool {
        InMemoryRegister::<u64, PAGE_DESCRIPTOR::Register>::new(self.0)
            .is_set(PAGE_DESCRIPTOR::VALID)
    }

    fn is_table_or_page(&self) -> bool {
        InMemoryRegister::<u64, PAGE_DESCRIPTOR::Register>::new(self.0)
            .is_set(PAGE_DESCRIPTOR::TYPE)
    }

    fn table_ptr(&self) -> Option<*mut PageTableManager> {
        if !self.is_valid() || !self.is_table_or_page() {
            return None;
        }
        let table_phys = self.0 & PAGE_DESCRIPTOR_ADDR_MASK;
        Some(kernel_phys_to_virt(table_phys as usize) as *mut PageTableManager)
    }
}

// This page table must be available before `init_runtime()` clears `.bss`,
// because we may set up EL1 MMU state while still running in EL2.
#[used]
#[link_section = ".data"]
static mut TABLE_MANAGER: PageTableManager = PageTableManager::new();

#[used]
#[link_section = ".data"]
static mut LINEARMAP_MANAGER: PageTableManager = PageTableManager::new();

#[repr(C, align(4096))]
pub struct PageTableManager([PageEntry; 512]);

impl PageTableManager {
    const fn new() -> Self {
        PageTableManager([PageEntry::new(); 512])
    }

    fn init() {
        let table = unsafe { &mut TABLE_MANAGER };
        for &base in crate::boards::MMU_L1_DEVICE_BASES {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set_block(base, MemAttributes::Device);
        }
        for &base in crate::boards::MMU_L1_NORMAL_BASES {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set_block(base, MemAttributes::Normal);
        }
    }

    fn init_linearmap() {
        let table = unsafe { &mut LINEARMAP_MANAGER };
        for &base in crate::boards::MMU_L1_DEVICE_BASES {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set_block(base, MemAttributes::Device);
        }
        for &base in crate::boards::MMU_L1_NORMAL_BASES {
            let index = (base >> 30) as usize;
            let _ = table.0[index].set_block(base, MemAttributes::Normal);
        }
    }
}

// Indicate whether the page table initialization is done.
static PAGETABLE_INIT_DONE: AtomicBool = AtomicBool::new(false);
static LINEARMAP_INIT_DONE: AtomicBool = AtomicBool::new(false);
static RUNTIME_LINEARMAP_INIT_DONE: AtomicBool = AtomicBool::new(false);
static RUNTIME_LINEARMAP_PHYS: AtomicUsize = AtomicUsize::new(0);

#[inline]
fn flush_tlb_all() {
    asm::tlbi_all();
    asm::dsb(DsbOptions::Sys);
    asm::isb_sy();
}

#[inline]
const fn page_table_index(addr: usize, shift: usize) -> usize {
    (addr >> shift) & PAGE_TABLE_INDEX_MASK
}

#[inline]
const fn align_down(addr: usize, align: usize) -> usize {
    addr & !(align - 1)
}

#[inline]
const fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

#[inline]
const fn is_valid_kernel_va(addr: usize) -> bool {
    (addr as u64).wrapping_sub(KERNEL_VIRT_START) < (1 << KERNEL_VA_BITS)
}

#[inline]
const fn is_valid_translation_va(addr: usize) -> bool {
    (addr as u64) < (1 << KERNEL_VA_BITS) || is_valid_kernel_va(addr)
}

pub fn alloc_page_table() -> Result<*mut PageTableManager, &'static str> {
    let raw = crate::allocator::malloc_align(
        mem::size_of::<PageTableManager>(),
        mem::align_of::<PageTableManager>(),
    );
    if raw.is_null() {
        return Err("failed to allocate page table");
    }

    unsafe {
        ptr::write_bytes(raw, 0, mem::size_of::<PageTableManager>());
    }

    Ok(raw.cast::<PageTableManager>())
}

fn next_level_table(entry: &mut PageEntry) -> Result<*mut PageTableManager, &'static str> {
    if !entry.is_valid() {
        let table = alloc_page_table()?;
        entry.set_table(table)?;
        return Ok(table);
    }

    entry.table_ptr().ok_or("page entry is not a page table")
}

fn map_page_in_pgtbl(
    pgtbl: &mut PageTableManager,
    va: usize,
    pa: usize,
    flags: MemAttributes,
) -> Result<(), &'static str> {
    let l1_table = next_level_table(&mut pgtbl.0[page_table_index(va, L1_SHIFT)])?;
    let l2_table = unsafe { &mut *l1_table };
    let l2_table = next_level_table(&mut l2_table.0[page_table_index(va, L2_SHIFT)])?;
    let l3_table = unsafe { &mut *l2_table };
    l3_table.0[page_table_index(va, L3_SHIFT)].set_page(pa as u64, flags)
}

/// Like `map_page_in_pgtbl`, but with EL0-accessible AP bits.
fn map_user_page_in_pgtbl(
    pgtbl: &mut PageTableManager,
    va: usize,
    pa: usize,
    flags: MemAttributes,
) -> Result<(), &'static str> {
    let l1_table = next_level_table(&mut pgtbl.0[page_table_index(va, L1_SHIFT)])?;
    let l2_table = unsafe { &mut *l1_table };
    let l2_table = next_level_table(&mut l2_table.0[page_table_index(va, L2_SHIFT)])?;
    let l3_table = unsafe { &mut *l2_table };
    l3_table.0[page_table_index(va, L3_SHIFT)]
        .set_page_with_ap(pa as u64, flags, PAGE_DESCRIPTOR::AP::EL0_RW.value)
}

// only supports L3 4KB granularity now
pub fn map_range_in_pgtbl(
    pgtbl: &mut PageTableManager,
    va: usize,
    pa: usize,
    len: usize,
    flags: MemAttributes,
) -> Result<(), &'static str> {
    if len == 0 {
        return Ok(());
    }
    if va & PAGE_MASK != 0 || pa & PAGE_MASK != 0 {
        return Err("virtual and physical addresses must be 4KB aligned");
    }

    let end = va
        .checked_add(len)
        .ok_or("virtual address range overflow")?;
    let _ = pa
        .checked_add(len)
        .ok_or("physical address range overflow")?;
    if !is_valid_translation_va(va) || !is_valid_translation_va(end - 1) {
        return Err("virtual address exceeds configured VA bits");
    }

    let mut cur_va = va;
    let mut cur_pa = pa;
    while cur_va < end {
        map_page_in_pgtbl(pgtbl, cur_va, cur_pa, flags)?;
        cur_va += PAGE_SIZE;
        cur_pa += PAGE_SIZE;
    }

    Ok(())
}

/// Map a contiguous range of pages into the page table with EL0-accessible
/// permissions (AP=EL0_RW, UXN=clear).
///
/// Wrapper around `map_user_page_in_pgtbl`.  Same alignment and overflow
/// checks as `map_range_in_pgtbl`.
pub(crate) fn map_user_range_in_pgtbl(
    pgtbl: &mut PageTableManager,
    va: usize,
    pa: usize,
    len: usize,
    flags: MemAttributes,
) -> Result<(), &'static str> {
    if len == 0 {
        return Ok(());
    }
    if va & PAGE_MASK != 0 || pa & PAGE_MASK != 0 {
        return Err("virtual and physical addresses must be 4KB aligned");
    }

    let end = va
        .checked_add(len)
        .ok_or("virtual address range overflow")?;
    let _ = pa
        .checked_add(len)
        .ok_or("physical address range overflow")?;
    if !is_valid_translation_va(va) || !is_valid_translation_va(end - 1) {
        return Err("virtual address exceeds configured VA bits");
    }

    let mut cur_va = va;
    let mut cur_pa = pa;
    while cur_va < end {
        map_user_page_in_pgtbl(pgtbl, cur_va, cur_pa, flags)?;
        cur_va += PAGE_SIZE;
        cur_pa += PAGE_SIZE;
    }

    Ok(())
}

fn unmap_page_in_pgtbl(pgtbl: &mut PageTableManager, va: usize) -> Result<(), &'static str> {
    let l1_entry = &mut pgtbl.0[page_table_index(va, L1_SHIFT)];
    let l1_table = l1_entry.table_ptr().ok_or("L1 entry is not mapped")?;
    let l2_table = unsafe { &mut *l1_table };
    let l2_entry = &mut l2_table.0[page_table_index(va, L2_SHIFT)];
    let l2_table = l2_entry.table_ptr().ok_or("L2 entry is not mapped")?;
    let l3_table = unsafe { &mut *l2_table };
    let l3_entry = &mut l3_table.0[page_table_index(va, L3_SHIFT)];
    if !l3_entry.is_valid() {
        return Err("L3 entry is not mapped");
    }
    l3_entry.0 = 0;
    Ok(())
}

pub fn unmap_range_in_pgtbl(
    pgtbl: &mut PageTableManager,
    va: usize,
    len: usize,
) -> Result<(), &'static str> {
    if len == 0 {
        return Ok(());
    }
    if va & PAGE_MASK != 0 {
        return Err("virtual address must be 4KB aligned");
    }

    let end = va
        .checked_add(len)
        .ok_or("virtual address range overflow")?;
    if !is_valid_translation_va(va) || !is_valid_translation_va(end - 1) {
        return Err("virtual address exceeds configured VA bits");
    }

    let mut cur_va = va;
    while cur_va < end {
        unmap_page_in_pgtbl(pgtbl, cur_va)?;
        cur_va += PAGE_SIZE;
    }

    Ok(())
}

/// Frees a page table allocated by [`alloc_page_table`] and all child page tables.
pub unsafe fn free_page_table(pgtbl: *mut PageTableManager) {
    unsafe fn free_page_table_level(pgtbl: *mut PageTableManager, level: usize) {
        if pgtbl.is_null() {
            return;
        }

        let table = unsafe { &mut *pgtbl };
        for entry in table.0.iter_mut() {
            if level < 2 {
                if let Some(next_table) = entry.table_ptr() {
                    free_page_table_level(next_table, level + 1);
                }
            }
            entry.0 = 0;
        }

        crate::allocator::free_align(pgtbl.cast::<u8>(), mem::align_of::<PageTableManager>());
    }

    free_page_table_level(pgtbl, 0);
}

pub fn init_el1_enable_mmu() {
    // Only allow CPU0 to initialize the page table, other cores wait
    let cpu_id = crate::arch::current_cpu_id();
    if cpu_id == 0 {
        PageTableManager::init();
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
            + TCR_EL1::T0SZ.val(TCR_TSZ),
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
    asm::isb_sy();
}

pub fn init_el1_boot_linearmap() {
    let cpu_id = crate::arch::current_cpu_id();
    if cpu_id == 0 {
        PageTableManager::init_linearmap();
        LINEARMAP_INIT_DONE.store(true, Ordering::Release);
        // Wake up all cores waiting on wfe
        unsafe {
            core::arch::asm!("sev", options(nostack, nomem));
        }
    } else {
        // Wait for CPU0 to finish linearmap table initialization.
        while !LINEARMAP_INIT_DONE.load(Ordering::Acquire) {
            unsafe {
                core::arch::asm!("wfe", options(nostack, nomem));
            }
        }
    }

    TTBR1_EL1.set(core::ptr::addr_of!(LINEARMAP_MANAGER) as u64);

    TCR_EL1.modify(
        TCR_EL1::TG1::KiB_4
            + TCR_EL1::SH1::InnerShareable
            + TCR_EL1::ORGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::IRGN1::WriteBack_ReadAlloc_WriteAlloc_Cacheable
            + TCR_EL1::EPD1::EnableTTBR1Walks
            + TCR_EL1::T1SZ.val(TCR_TSZ),
    );

    flush_tlb_all();
}

pub fn init_el1_runtime_linearmap() -> Result<(), &'static str> {
    let cpu_id = crate::arch::current_cpu_id();
    if cpu_id == 0 {
        let runtime_linearmap = alloc_page_table()?;
        let runtime_linearmap_table = unsafe { &mut *runtime_linearmap };
        for &base in crate::boards::MMU_L1_DEVICE_BASES {
            let aligned_base = align_down(base as usize, L1_BLOCK_SIZE as usize);
            map_range_in_pgtbl(
                runtime_linearmap_table,
                kernel_phys_to_virt(aligned_base),
                aligned_base,
                L1_BLOCK_SIZE as usize,
                MemAttributes::Device,
            )?;
        }
        for &base in crate::boards::MMU_L1_NORMAL_BASES {
            let aligned_base = align_down(base as usize, L1_BLOCK_SIZE as usize);

            // Map the intersection between this L1 block and the physical DRAM range.
            let dram_base = crate::boards::PHYS_DRAM_BASE as usize;
            let dram_size = crate::boards::PHYS_DRAM_SIZE as usize;
            let dram_end = dram_base
                .checked_add(dram_size)
                .ok_or("DRAM range overflow")?;

            let block_start = aligned_base;
            let block_end = aligned_base + L1_BLOCK_SIZE as usize;

            let map_start = core::cmp::max(block_start, dram_base);
            let map_end = core::cmp::min(block_end, dram_end);

            if map_start < map_end {
                let map_start_aligned = align_down(map_start, PAGE_SIZE);
                let map_end_aligned = align_up(map_end, PAGE_SIZE);
                let map_len = map_end_aligned.saturating_sub(map_start_aligned);

                map_range_in_pgtbl(
                    runtime_linearmap_table,
                    kernel_phys_to_virt(map_start_aligned),
                    map_start_aligned,
                    map_len,
                    MemAttributes::Normal,
                )?;
            }
        }

        asm::dsb(DsbOptions::Sys);

        let runtime_linearmap_phys = kernel_virt_to_phys(runtime_linearmap as usize);
        RUNTIME_LINEARMAP_PHYS.store(runtime_linearmap_phys, Ordering::Release);
        RUNTIME_LINEARMAP_INIT_DONE.store(true, Ordering::Release);
        // Wake up all cores waiting on wfe
        unsafe {
            core::arch::asm!("sev", options(nostack, nomem));
        }
    } else {
        // Wait for CPU0 to finish runtime linearmap table initialization.
        while !RUNTIME_LINEARMAP_INIT_DONE.load(Ordering::Acquire) {
            unsafe {
                core::arch::asm!("wfe", options(nostack, nomem));
            }
        }
    }

    let runtime_linearmap_phys = RUNTIME_LINEARMAP_PHYS.load(Ordering::Acquire);

    asm::dsb(DsbOptions::Sys);
    TTBR1_EL1.set(runtime_linearmap_phys as u64);

    flush_tlb_all();
    Ok(())
}
