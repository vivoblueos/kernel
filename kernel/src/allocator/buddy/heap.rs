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

use crate::{mm::kernel_virt_to_phys, sync::spinlock::SpinLock};
use allocator_crate::buddy::{
    BuddyAllocator, BuddyInitError, BuddyMemoryInfo, PAGE_SHIFT, PAGE_SIZE,
};
use core::{cell::UnsafeCell, ptr::NonNull};

/// Virtual address marking the end of the kernel image, provided by the
/// linker script. It is typically aligned to `PAGE_SIZE`.
unsafe extern "C" {
    static mut _end: u8;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BuddyLayoutError {
    InvalidPhysicalRange,
    AddressOverflow,
    MetadataOutsidePhysicalMemory,
    Allocator(BuddyInitError),
}

impl From<BuddyInitError> for BuddyLayoutError {
    fn from(value: BuddyInitError) -> Self {
        Self::Allocator(value)
    }
}

// BuddyLayout includes:
// 1. The virtual address of the metadata start
// 2. The length of the metadata
// 3. The total number of pages in the physical DRAM
// 4. The starting page frame number that the buddy allocator can actually manage
//    (the first page frame that can actually be managed after skipping the kernel image
//     and metadata pages)
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct BuddyLayout {
    pub(super) metadata_virt_start: usize,
    pub(super) metadata_len: usize,
    pub(super) total_pages: usize,
    pub(super) manageable_start_pfn: usize,
}

fn checked_align_up(value: usize, align: usize) -> Option<usize> {
    value.checked_add(align - 1).map(|v| v & !(align - 1))
}

// Three parameters:
// 1. Physical address range start
// 2. Physical address range end
// 3. Kernel image end virtual address
pub(super) fn get_buddy_layout(
    phys_start: usize,
    phys_end: usize,
    kernel_end_virt: usize,
) -> Result<BuddyLayout, BuddyLayoutError> {
    // Validate physical address range: start < end, both aligned to PAGE_SIZE
    if phys_start >= phys_end
        || phys_start & (PAGE_SIZE - 1) != 0
        || phys_end & (PAGE_SIZE - 1) != 0
    {
        return Err(BuddyLayoutError::InvalidPhysicalRange);
    }

    // Calculate the total number of pages in the physical memory region
    let total_pages = (phys_end - phys_start) >> PAGE_SHIFT;
    // Calculate metadata layout (size and alignment)
    let metadata_layout = BuddyAllocator::metadata_layout(total_pages)?;
    // Metadata starts immediately after the kernel image end, aligned up to PAGE_SIZE
    let metadata_virt_start =
        checked_align_up(kernel_end_virt, PAGE_SIZE).ok_or(BuddyLayoutError::AddressOverflow)?;
    // manageable_virt_start is the first address available for the buddy allocator
    // to manage. It skips pages occupied by the kernel image and metadata, aligned to PAGE_SIZE.
    let metadata_virt_end = metadata_virt_start
        .checked_add(metadata_layout.size())
        .ok_or(BuddyLayoutError::AddressOverflow)?;
    let manageable_virt_start =
        checked_align_up(metadata_virt_end, PAGE_SIZE).ok_or(BuddyLayoutError::AddressOverflow)?;

    // Verify that metadata resides within the physical memory range
    let metadata_phys_start = kernel_virt_to_phys(metadata_virt_start);
    let metadata_phys_end = kernel_virt_to_phys(metadata_virt_end);
    if metadata_phys_start < phys_start || metadata_phys_end > phys_end {
        return Err(BuddyLayoutError::MetadataOutsidePhysicalMemory);
    }

    // Construct and return the BuddyLayout
    let manageable_phys_start = kernel_virt_to_phys(manageable_virt_start);
    Ok(BuddyLayout {
        metadata_virt_start,
        metadata_len: metadata_layout.size(),
        total_pages,
        manageable_start_pfn: (manageable_phys_start - phys_start) >> PAGE_SHIFT,
    })
}

/// Immutable address-translation metadata captured during buddy initialization.
///
/// This snapshot is published before concurrent allocator access begins and is
/// never modified afterwards, so address conversion does not require the
/// allocator lock.
struct BuddyTranslation {
    phys_base: usize,
    total_pages: usize,
    initialized: bool,
}

impl BuddyTranslation {
    const fn new() -> Self {
        Self {
            phys_base: 0,
            total_pages: 0,
            initialized: false,
        }
    }

    fn pfn_to_phys(&self, pfn: usize) -> Option<usize> {
        if !self.initialized || pfn >= self.total_pages {
            return None;
        }
        pfn.checked_shl(PAGE_SHIFT as u32)
            .and_then(|offset| self.phys_base.checked_add(offset))
    }

    fn phys_to_pfn(&self, phys_addr: usize) -> Option<usize> {
        if !self.initialized || phys_addr & (PAGE_SIZE - 1) != 0 {
            return None;
        }
        let offset = phys_addr.checked_sub(self.phys_base)?;
        let pfn = offset >> PAGE_SHIFT;
        (pfn < self.total_pages).then_some(pfn)
    }
}

/// Kernel synchronization and physical-address wrapper for the raw buddy.
pub(in crate::allocator) struct BuddyHeap {
    allocator: SpinLock<BuddyAllocator>,
    translation: UnsafeCell<BuddyTranslation>,
}

impl BuddyHeap {
    pub(in crate::allocator) const fn new() -> Self {
        Self {
            allocator: SpinLock::new(BuddyAllocator::new()),
            translation: UnsafeCell::new(BuddyTranslation::new()),
        }
    }

    fn translation(&self) -> &BuddyTranslation {
        // SAFETY: `init` publishes this snapshot before concurrent access to
        // the heap begins, and the snapshot is immutable after publication.
        unsafe { &*self.translation.get() }
    }

    /// Initialize the global physical page allocator.
    ///
    /// # Safety
    ///
    /// `phys_start..phys_end` must be valid writable DRAM, must contain the
    /// kernel image and metadata selected from `_end`, and must remain owned by
    /// the allocator for the rest of the boot. This method must be called once,
    /// before the heap is accessed from any other execution context.
    pub(in crate::allocator) unsafe fn init(&self, phys_start: usize, phys_end: usize) {
        let buddy_layout =
            get_buddy_layout(phys_start, phys_end, core::ptr::addr_of_mut!(_end) as usize)
                .expect("invalid kernel buddy metadata layout");
        let metadata_ptr = NonNull::new(buddy_layout.metadata_virt_start as *mut u8)
            .expect("buddy metadata pointer must not be null");
        let mut allocator = self.allocator.irqsave_lock();
        allocator
            .init(
                metadata_ptr,
                buddy_layout.metadata_len,
                buddy_layout.total_pages,
                buddy_layout.manageable_start_pfn..buddy_layout.total_pages,
            )
            .expect("failed to initialize raw buddy allocator");
        // SAFETY: the caller guarantees one-time initialization before any
        // concurrent access, and this is the snapshot's only post-construction
        // write.
        unsafe {
            *self.translation.get() = BuddyTranslation {
                phys_base: phys_start,
                total_pages: buddy_layout.total_pages,
                initialized: true,
            };
        }
    }

    pub(in crate::allocator) fn alloc_pages_phys_addr(&self, order: usize) -> Option<usize> {
        let frame = self.allocator.irqsave_lock().alloc_pages(order)?;
        self.translation().pfn_to_phys(frame.pfn())
    }

    pub(in crate::allocator) fn alloc_pages_pfn(&self, order: usize) -> Option<usize> {
        self.allocator
            .irqsave_lock()
            .alloc_pages(order)
            .map(|f| f.pfn())
    }

    #[allow(dead_code)]
    pub(in crate::allocator) fn alloc_pages_aligned_phys_addr(
        &self,
        order: usize,
        align_order: usize,
    ) -> Option<usize> {
        let frame = self
            .allocator
            .irqsave_lock()
            .alloc_pages_aligned(order, align_order)?;
        self.translation().pfn_to_phys(frame.pfn())
    }

    /// Release a physical block returned by [`Self::alloc_pages_phys_addr`].
    ///
    /// # Safety
    ///
    /// `phys_addr` must be the address of a live block from this heap, `order`
    /// must match its allocation order, and the block must be released once.
    pub(in crate::allocator) unsafe fn free_pages_phys_addr(&self, phys_addr: usize, order: usize) {
        let pfn = self
            .phys_to_pfn(phys_addr)
            .expect("invalid physical address passed to buddy free");
        self.allocator.irqsave_lock().free_pages_pfn(pfn, order);
    }

    /// Release pages by PFN.
    ///
    /// # Safety
    ///
    /// `pfn` must identify the head of a live allocation from this heap,
    /// `order` must match its allocation order, and the block must be released
    /// exactly once.
    pub(in crate::allocator) unsafe fn free_pages_pfn(&self, pfn: usize, order: usize) {
        self.allocator.irqsave_lock().free_pages_pfn(pfn, order);
    }

    pub(in crate::allocator) fn phys_to_pfn(&self, phys_addr: usize) -> Option<usize> {
        self.translation().phys_to_pfn(phys_addr)
    }

    pub(in crate::allocator) fn pfn_to_phys(&self, pfn: usize) -> Option<usize> {
        self.translation().pfn_to_phys(pfn)
    }

    #[allow(dead_code)]
    pub(in crate::allocator) fn memory_info(&self) -> BuddyMemoryInfo {
        self.allocator.irqsave_lock().memory_info()
    }

    #[cfg(test)]
    /// Initialize an independently owned heap for a test fixture.
    ///
    /// # Safety
    ///
    /// `metadata..metadata + metadata_len` must satisfy
    /// [`BuddyAllocator::init`]'s ownership, alignment, and lifetime
    /// requirements. `self` must already be at its final address, and the
    /// metadata must outlive it. The physical range described by `phys_base`
    /// and `total_pages` must remain exclusively owned by the fixture whenever
    /// a returned address is dereferenced. The heap must not have been
    /// initialized before, and its translation snapshot must not be changed
    /// after this call becomes visible to another execution context.
    pub(super) unsafe fn init_for_test(
        &self,
        phys_base: usize,
        total_pages: usize,
        manageable_start_pfn: usize,
        metadata: NonNull<u8>,
        metadata_len: usize,
    ) -> Result<(), BuddyInitError> {
        let mut allocator = self.allocator.irqsave_lock();
        allocator.init(
            metadata,
            metadata_len,
            total_pages,
            manageable_start_pfn..total_pages,
        )?;
        // SAFETY: test callers initialize a fresh heap before sharing or using
        // it, and never mutate its translation snapshot afterwards.
        *self.translation.get() = BuddyTranslation {
            phys_base,
            total_pages,
            initialized: true,
        };
        Ok(())
    }
}
