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

pub mod first_fit;
pub mod mapper;

use core::sync::atomic::{AtomicBool, Ordering};

use crate::mm::{
    memory_bank::MemoryBank, CachePolicy, MemAttribute, MemFlags, MemType, PhysicalAddress,
};

// Used before BSS initialization; retain publication when CPU0 clears BSS so
// secondary CPUs can still enter through the shared bootstrap table.
#[cfg_attr(compatible_old_toolchain, link_section = ".data")]
#[cfg_attr(not(compatible_old_toolchain), unsafe(link_section = ".data"))]
static PAGETABLE_INIT_DONE: AtomicBool = AtomicBool::new(false);

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct PageEntry(usize);

// Safety: Only be used before the MMU is enabled.
pub unsafe extern "C" fn init_boot_pgtable<P: PageFormat>() -> usize {
    let cpu_id = crate::arch::current_cpu_id();

    unsafe extern "C" {
        static mut BOOT_PAGE_TABLE: u8;
    }

    let phys_addr: usize;
    unsafe {
        // Load the absolute physical address defined by the linker script.
        core::arch::asm!(
            "ldr {addr}, ={table}",
            addr = out(reg) phys_addr,
            table = sym BOOT_PAGE_TABLE,
            options(readonly, nostack, preserves_flags),
        );
    }

    if cpu_id == 0 {
        assert!(matches!(P::LEVELS, 3 | 4));
        let entry_count = P::PAGE_SIZE / size_of::<PageEntry>();
        // Both formats use L1 blocks (1 GiB). The 48-bit format adds an L0
        // root: L0 block descriptors are not valid with a 4 KiB granule.
        let block_level = P::LEVELS - 3;
        let table_count = usize::from(P::LEVELS - 2);
        let block_size = P::PAGE_SIZE * entry_count.pow(2);
        let entries_ptr = phys_addr as *mut PageEntry;
        unsafe {
            core::ptr::write_bytes(entries_ptr, 0, entry_count * table_count);
            let tables = core::slice::from_raw_parts_mut(entries_ptr, entry_count * table_count);
            let entries = if P::LEVELS == 4 {
                let (root, blocks) = tables.split_at_mut(entry_count);
                let descriptor = PageEntry(P::table_descriptor(phys_addr + P::PAGE_SIZE));
                // The configured 32-bit physical aperture fits in one L1
                // table, shared by the identity and kernel direct mappings.
                root[P::get_index(0, 0)] = descriptor;
                root[P::get_index(crate::mm::KERNEL_VIRT_OFFSET, 0)] = descriptor;
                blocks
            } else {
                tables
            };

            for bank in crate::boards::MEMORY_BANKS {
                let ((start, end), attributes) = match bank {
                    MemoryBank::MMIO(range) => (
                        range,
                        MemAttribute {
                            flags: MemFlags::READ | MemFlags::WRITE | MemFlags::GLOBAL,
                            memory_type: MemType::Device,
                        },
                    ),
                    MemoryBank::RAM(range) => (
                        range,
                        MemAttribute {
                            flags: MemFlags::READ | MemFlags::WRITE | MemFlags::EXECUTE,
                            memory_type: MemType::Normal(CachePolicy::WriteBack),
                        },
                    ),
                };
                if start.into_raw() >= end.into_raw() {
                    continue;
                }
                // Cover every block intersecting the bank's [start, end) range.
                let start = start.into_raw() & !(block_size - 1);
                for base in (start..end.into_raw()).step_by(block_size) {
                    let index = P::get_index(base, block_level);
                    entries[index] = PageEntry(P::get_translate(base, attributes, true));
                }
            }
        }
        PAGETABLE_INIT_DONE.store(true, Ordering::Release);
    } else {
        while !PAGETABLE_INIT_DONE.load(Ordering::Acquire) {
            core::hint::spin_loop();
        }
    }
    phys_addr
}

pub trait PageFormat {
    const PAGE_SIZE: usize;
    const LEVELS: u8;
    const VIRT_ADDR_BITS: u8;
    const PHYS_ADDR_BITS: u8;

    fn get_translate(base: usize, att: MemAttribute, is_block: bool) -> usize;
    fn get_index(base: usize, level: u8) -> usize;
    /// Encode a descriptor pointing to the next page-table level.
    fn table_descriptor(base: usize) -> usize;
    /// Decode a table/page descriptor; invalid and block entries return None.
    fn table_address(entry: usize) -> Option<usize>;
    fn is_valid(entry: usize) -> bool;
}

#[derive(Debug)]
pub struct FrameUsage {
    used: usize,
    total: usize,
}

/// Physical page counts, with reserved pages excluded from allocation peaks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FrameStats {
    pub total: usize,
    pub reserved: usize,
    pub allocated: usize,
    pub free: usize,
    pub peak_allocated: usize,
}

impl FrameUsage {
    pub fn new(used: usize, total: usize) -> Self {
        FrameUsage { used, total }
    }

    pub fn total(&self) -> usize {
        self.total
    }

    pub fn used(&self) -> usize {
        self.used
    }

    pub fn free(&self) -> usize {
        self.total - self.used
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FrameDeallocationError {
    NotInitialized,
    InvalidRange,
    Reserved,
    NotAllocated,
}

/// Exclusive ownership of physical page frames.
///
/// Methods use shared references; implementations must synchronize concurrent
/// access to shared allocator state internally, including access through
/// different handles to the same frame pool. Callers do not need an external
/// lock to serialize allocation, deallocation, or usage queries.
///
/// # Safety
/// Allocations must be aligned, disjoint, writable through the kernel direct
/// map, and remain live until explicitly freed. Failed allocation must not
/// consume frames. Reserved memory must never be returned or freed. These
/// guarantees must hold under concurrent calls as well.
pub unsafe trait FrameAllocator {
    fn alloc_frame(&self) -> Option<PhysicalAddress>;

    /// # Safety
    /// The caller must own this live allocation, with no remaining users or
    /// hardware translations, and must release it exactly once.
    fn free_frame(&self, frame: PhysicalAddress) -> Result<(), FrameDeallocationError>;

    fn usage(&self) -> FrameUsage;
}
