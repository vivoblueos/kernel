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

use super::page::{LinkedList, Page, PageFlags, MAX_ORDER, PAGE_SHIFT, PAGE_SIZE};
use crate::{
    mm::{kernel_phys_to_virt, kernel_virt_to_phys},
    sync::spinlock::SpinLock,
};
use core::ptr;

extern "C" {
    static mut _end: u8;
}

/// Calculate the minimum order required to hold `size` bytes.
#[inline]
pub const fn order_of_size(size: usize) -> usize {
    let pages = (size + PAGE_SIZE - 1) >> PAGE_SHIFT;
    if pages <= 1 {
        0
    } else {
        pages.next_power_of_two().trailing_zeros() as usize
    }
}

/// Buddy allocator memory statistics.
#[derive(Debug, Clone, Copy)]
pub struct BuddyMemoryInfo {
    pub total_pages: usize,
    pub free_pages: usize,
    pub used_pages: usize,
    pub reserved_pages: usize,
}

/// Core buddy allocator state (protected by `SpinLock` in [`BuddyAllocator`]).
pub struct BuddyAllocatorCore {
    /// Free page block list heads for each order.
    free_lists: [LinkedList; MAX_ORDER + 1],
    /// Total number of physical pages.
    total_pages: usize,
    /// First available pfn (after metadata region).
    start_pfn: usize,
    /// Physical memory upper limit pfn.
    end_pfn: usize,
    /// Base physical address of managed memory.
    base_addr: usize,
    /// Pointer to the Page descriptor array.
    pages: *mut Page,
}

impl BuddyAllocatorCore {
    pub const fn new() -> Self {
        BuddyAllocatorCore {
            free_lists: [LinkedList::new(); MAX_ORDER + 1],
            total_pages: 0,
            start_pfn: 0,
            end_pfn: 0,
            base_addr: 0,
            pages: ptr::null_mut(),
        }
    }

    /// Initialize the buddy allocator.
    ///
    /// # Safety
    /// `phys_mem_start..phys_mem_end` must be valid, exclusively owned, writable physical memory.
    /// This function overwrites the beginning of this region with metadata.
    ///
    /// # Algorithm
    /// 1. Compute total pages from the physical memory range.
    /// 2. Reserve the memory for `struct Page[total_pages]` metadata.
    /// 3. Zero and initialize each page descriptor / struct Page (pfn, flags).
    /// 4. Mark metadata pages as RESERVED.
    /// 5. Add remaining free pages to free lists as largest possible aligned blocks.
    ///    Each block starts at a pfn aligned to its size (buddy invariant).
    pub unsafe fn init(&mut self, phys_mem_start: usize, phys_mem_end: usize) {
        self.base_addr = phys_mem_start;
        self.total_pages = (phys_mem_end - phys_mem_start) >> PAGE_SHIFT;
        self.end_pfn = self.total_pages; // 数组上 end_pfn 不可用

        // Reserve space for struct Page[total_pages] after the kernel image and static heap.
        let virt_mem_start = kernel_phys_to_virt(phys_mem_start);
        let mut virt_page_array_start =
            crate::support::align_up_size(unsafe { ptr::addr_of_mut!(_end) as usize }, PAGE_SIZE);
        assert!(virt_page_array_start >= virt_mem_start);

        let page_array_size = self.total_pages * core::mem::size_of::<Page>();
        let virt_page_array_end = virt_page_array_start + page_array_size;

        // Align metadata end up to PAGE_SIZE boundary.
        let virt_metadata_end = crate::support::align_up_size(virt_page_array_end, PAGE_SIZE);
        let phys_metadata_end = kernel_virt_to_phys(virt_metadata_end);
        assert!(phys_metadata_end <= phys_mem_end);
        // start_pfn 指的是第一个可用的物理页的 pfn，因此它是 metadata 结束后的第一个页的 pfn。
        self.start_pfn = (phys_metadata_end - phys_mem_start) >> PAGE_SHIFT;

        // Zero the entire page descriptor array / struct Page array.
        core::ptr::write_bytes(virt_page_array_start as *mut u8, 0, page_array_size);
        // 把 pages 指针指向这个数组的起始位置，后续通过 pfn 索引访问对应的 Page 结构体。
        self.pages = virt_page_array_start as *mut Page;

        // Initialize each page descriptor / struct Page.
        for pfn in 0..self.total_pages {
            let page = &mut *self.pages.add(pfn);
            page.pfn = pfn;
        }

        // Mark dram_start...page_array_end pages as RESERVED.
        for pfn in 0..self.start_pfn {
            let page = &mut *self.pages.add(pfn);
            page.flags.set(PageFlags::RESERVED);
        }

        // Add remaining pages to free lists as largest possible aligned blocks.
        let mut pfn = self.start_pfn;
        while pfn < self.end_pfn {
            let remaining = self.end_pfn - pfn;
            // usize::BITS - 1 - remaining.leading_zeros() = floor(log2(remaining))
            let max_order = MAX_ORDER.min((usize::BITS - 1 - remaining.leading_zeros()) as usize);
            let order = (0..=max_order)
                .rev()
                .find(|&o| pfn % (1 << o) == 0)
                .expect("order 0 must always satisfy buddy block alignment");

            let page = &mut *self.pages.add(pfn);
            page.flags.set(PageFlags::FREE);
            page.order = order as u8;
            unsafe {
                self.free_lists[order].push(page);
            }

            pfn += 1 << order;
        }
    }

    /// Allocate `2^order` contiguous physical pages.
    ///
    /// # Algorithm
    /// Search upward from `order` to `MAX_ORDER` for a free block.
    /// When a larger block is found, repeatedly split it in half
    /// until it reaches the requested size, pushing the unused buddy
    /// half back onto the appropriate free list each time.
    pub fn alloc_pages(&mut self, order: usize) -> Option<*mut Page> {
        self.alloc_pages_from(order, order)
    }

    /// Allocate `2^order` contiguous physical pages aligned to `2^align_order` pages.
    pub fn alloc_pages_aligned(&mut self, order: usize, align_order: usize) -> Option<*mut Page> {
        log::info!(
            "alloc_pages_aligned: order={}, align_order={}",
            order,
            align_order
        );
        self.alloc_pages_from(order, order.max(align_order))
    }

    /// Common allocation logic.
    ///
    /// `order` is the requested allocation size, expressed as `2^order` pages.
    /// `search_order` is the minimum free-list order to search from; it may be
    /// larger than `order` when extra alignment is required.
    fn alloc_pages_from(&mut self, order: usize, search_order: usize) -> Option<*mut Page> {

        log::info!(
            "alloc_pages_from: order={} or search_order={}",
            order,
            search_order
        );

        if order > MAX_ORDER || search_order > MAX_ORDER {
            return None;
        }

        for o in search_order..=MAX_ORDER {
            let page_ptr = match unsafe { self.free_lists[o].pop() } {
                Some(p) => p,
                None => continue,
            };
            let mut current_order = o;

            log::info!(
                "alloc_pages_from: current_order={}",
                current_order
            );

            debug_assert!(unsafe { (*page_ptr).flags.contains(PageFlags::FREE) });

            while current_order > order {
                current_order -= 1;
                let buddy_pfn = unsafe { (*page_ptr).pfn } ^ (1 << current_order);
                debug_assert!(buddy_pfn == unsafe { (*page_ptr).pfn } + (1 << current_order));
                let buddy = unsafe { &mut *self.pfn_to_virt(buddy_pfn) };
                buddy.flags.set(PageFlags::FREE);
                buddy.order = current_order as u8;

                log::info!(
                    "alloc_pages_from: buddy_pfn={}",
                    buddy_pfn
                );

                unsafe {
                    self.free_lists[current_order].push(buddy);
                }
            }

            debug_assert!(current_order == order);

            let page = unsafe { &mut *page_ptr };
            page.flags.clear(PageFlags::FREE);
            page.order = order as u8;

            log::info!(
                "alloc_pages_from exit: page pfn={}, order={}",
                page.pfn,
                page.order
            );

            return Some(page_ptr);
        }

        None
    }

    /// Free a block of `2^order` pages starting at `page`.
    ///
    /// # Safety
    /// `page` must be the head page of an allocated block of the given `order`.
    ///
    /// # Algorithm — Coalesce (Buddy Merging)
    /// 1. Mark the page as FREE and set its current order.
    /// 2. Compute the buddy pfn using XOR with the block size (`pfn ^ (1 << order)`).
    ///    This works because buddies are always at addresses that differ by exactly
    ///    the block size, and their lower `order` bits are complements.
    /// 3. If the buddy is free and has the same order, remove it from its free list,
    ///    merge the two blocks into a single block of `order + 1`, and repeat.
    /// 4. If the buddy is not free, has a different order, or is outside the managed
    ///    range, stop and push the current block onto the free list.
    pub unsafe fn free_pages(&mut self, page: &mut Page, order: usize) {
        debug_assert!(
            page.pfn & ((1 << order) - 1) == 0,
            "free_pages: page must be block head"
        );

        let mut current_page = page;
        let mut current_order = order;

        current_page.flags.set(PageFlags::FREE);
        current_page.order = current_order as u8;
        log::info!(
            "free_pages: current block pfn={}, order={}",
            current_page.pfn,
            current_page.order
        );

        while current_order < MAX_ORDER {
            let buddy_pfn = current_page.pfn ^ (1 << current_order);

            log::info!(
                "free_pages: buddy pfn={}, current_order={}",
                buddy_pfn,
                current_order
            );

            if buddy_pfn >= self.end_pfn || buddy_pfn < self.start_pfn {
                break;
            }

            let buddy = &mut *self.pfn_to_virt(buddy_pfn);
            log::info!(
                "free_pages: buddy is_free={}, order={}",
                buddy.flags.contains(PageFlags::FREE),
                buddy.order
            );

            // A free buddy with a smaller order means this buddy range has been
            // split into smaller blocks: the page at buddy_pfn may be a free
            // block head, but the whole current-order buddy range is not free.
            // A free buddy can never have a larger order than the current block;
            // before it could become a larger block, it would have to merge with
            // the current block first.
            if !buddy.flags.contains(PageFlags::FREE) || (buddy.order as usize) < current_order {
                break;
            }
            debug_assert!(
                (buddy.order as usize) == current_order,
                "free buddy cannot have a larger order than current block"
            );

            log::info!(
                "free_pages: remove buddy from free_lists, buddy_pfn={}, order={}",
                buddy_pfn,
                current_order
            );
            self.free_lists[current_order].remove(buddy);

            if buddy_pfn < current_page.pfn {
                current_page.flags.clear(PageFlags::FREE);
                current_page.order = 0;
                current_page = buddy;
            } else {
                buddy.flags.clear(PageFlags::FREE);
                buddy.order = 0;
            }
            current_order += 1;
            current_page.order = current_order as u8;
        }

        log::info!(
            "free_pages: push block to free_lists, pfn={}, order={}",
            current_page.pfn,
            current_order
        );
        self.free_lists[current_order].push(current_page);
    }

    /// Return the physical address for a page pfn.
    pub fn pfn_to_phys(&self, pfn: usize) -> usize {
        self.base_addr + (pfn << PAGE_SHIFT)
    }

    /// Get a mutable pointer to the `Page` descriptor for `pfn`.
    pub(crate) fn pfn_to_virt(&mut self, pfn: usize) -> *mut Page {
        debug_assert!(pfn < self.total_pages);
        unsafe { self.pages.add(pfn) }
    }

    /// Get memory statistics.
    pub fn memory_info(&self) -> BuddyMemoryInfo {
        let mut free_pages = 0;

        for order in 0..=MAX_ORDER {
            let mut count = 0;
            let mut node = self.free_lists[order].peek();
            while let Some(ptr) = node {
                count += 1;
                let (pfn, next) = unsafe { ((*ptr).pfn, (*ptr).list.next) };
                log::info!(
                    "buddy free list block: order={}, pfn={}, phys={:#x}",
                    order,
                    pfn,
                    self.pfn_to_phys(pfn)
                );
                node = if next.is_null() { None } else { Some(next) };
            }
            free_pages += count * (1 << order);
        }

        let reserved_pages = self.start_pfn;
        let used_pages = self.total_pages.saturating_sub(free_pages + reserved_pages);

        BuddyMemoryInfo {
            total_pages: self.total_pages,
            free_pages,
            used_pages,
            reserved_pages,
        }
    }
}

/// SpinLock-wrapped buddy allocator.
///
/// All public methods are thread-safe — the lock is acquired internally.
pub struct BuddyAllocator {
    inner: SpinLock<BuddyAllocatorCore>,
}

impl BuddyAllocator {
    pub const fn new() -> Self {
        BuddyAllocator {
            inner: SpinLock::new(BuddyAllocatorCore::new()),
        }
    }

    /// Initialize the buddy allocator with a physical memory range.
    ///
    /// # Safety
    /// `phys_mem_start..phys_mem_end` must be valid, exclusively owned, writable physical memory.
    pub unsafe fn init(&self, phys_mem_start: usize, phys_mem_end: usize) {
        let mut inner = self.inner.irqsave_lock();
        inner.init(phys_mem_start, phys_mem_end);
    }

    /// Allocate `2^order` contiguous physical pages.
    pub fn alloc_pages(&self, order: usize) -> Option<*mut Page> {
        let mut inner = self.inner.irqsave_lock();
        inner.alloc_pages(order)
    }

    /// Allocate `2^order` contiguous physical pages aligned to `2^align_order` pages.
    pub fn alloc_pages_aligned(&self, order: usize, align_order: usize) -> Option<*mut Page> {
        let mut inner = self.inner.irqsave_lock();
        log::info!(
            "alloc_pages_aligned: order={}, align_order={}",
            order,
            align_order
        );
        inner.alloc_pages_aligned(order, align_order)
    }

    /// Allocate pages and return the physical address.
    pub fn alloc_pages_phys_addr(&self, order: usize) -> Option<usize> {
        let mut inner = self.inner.irqsave_lock();
        inner.alloc_pages(order).map(|p| {
            let pfn = unsafe { (*p).pfn };
            inner.pfn_to_phys(pfn)
        })
    }

    /// Free a block of pages.
    ///
    /// # Safety
    /// `page` must be the head of an allocated block of the given `order`.
    pub unsafe fn free_pages(&self, page: &mut Page, order: usize) {
        let mut inner = self.inner.irqsave_lock();
        inner.free_pages(page, order);
    }

    /// Free pages by pfn.
    ///
    /// # Safety
    /// `pfn` must be the head of an allocated block of the given `order`.
    pub unsafe fn free_pages_pfn(&self, pfn: usize, order: usize) {
        let mut inner = self.inner.irqsave_lock();
        let page = &mut *inner.pfn_to_virt(pfn);
        inner.free_pages(page, order);
    }

    /// Convert pfn to Page descriptor pointer.
    ///
    /// Returns a mutable pointer to the `Page` descriptor for the given `pfn`.
    pub fn pfn_to_virt(&self, pfn: usize) -> *mut Page {
        let mut inner = self.inner.irqsave_lock();
        inner.pfn_to_virt(pfn)
    }

    /// Convert pfn to physical address.
    pub fn pfn_to_phys(&self, pfn: usize) -> usize {
        let mut inner = self.inner.irqsave_lock();
        inner.pfn_to_phys(pfn)
    }

    /// Get memory statistics.
    pub fn memory_info(&self) -> BuddyMemoryInfo {
        let inner = self.inner.irqsave_lock();
        inner.memory_info()
    }
}
