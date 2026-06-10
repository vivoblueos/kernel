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

//! Buddy allocator unit tests.
//!
//! These tests require a real physical memory region to run.
//! They are intended to be run in a kernel test harness with a
//! reserved test memory region.

use super::{
    heap::{order_of_size, BuddyAllocatorCore, BuddyMemoryInfo},
    page::{PageFlags, MAX_ORDER, PAGE_SIZE},
};
use alloc::vec::Vec;
use core::sync::atomic::Ordering;

// 16 MiB test memory region — adjust based on test harness.
const TEST_MEM_SIZE: usize = 16 * 1024 * 1024;

fn alloc_test_mem() -> (*mut u8, usize) {
    // Test harness must provide a raw memory region.
    // For kernel tests, this can be a reserved static buffer.
    unimplemented!("test harness must provide test memory region")
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper functions
// ─────────────────────────────────────────────────────────────────────────────

fn check_conservation(core: &BuddyAllocatorCore) {
    let info = core.memory_info();
    assert_eq!(
        info.total_pages,
        info.free_pages + info.used_pages + info.reserved_pages,
        "page conservation violated: total={} free={} used={} reserved={}",
        info.total_pages,
        info.free_pages,
        info.used_pages,
        info.reserved_pages
    );
}

fn count_free_list_pages(core: &BuddyAllocatorCore) -> usize {
    let info = core.memory_info();
    info.free_pages
}

// ─────────────────────────────────────────────────────────────────────────────
// Basic allocation / deallocation
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod basic_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn init_creates_valid_state() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let info = core.memory_info();
        assert!(info.total_pages > 0);
        assert!(info.reserved_pages > 0);
        check_conservation(&core);
    }

    #[test]
    fn alloc_single_page() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before_free = core.memory_info().free_pages;
        let page = core
            .alloc_pages(0)
            .expect("alloc single page should succeed");
        let after_free = core.memory_info().free_pages;

        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        assert_eq!(unsafe { (*page).order }, 0);
        assert_eq!(after_free, before_free - 1);
        check_conservation(&core);

        unsafe { core.free_pages(&mut *page, 0) };
        let final_free = core.memory_info().free_pages;
        assert_eq!(final_free, before_free);
        check_conservation(&core);
    }

    #[test]
    fn alloc_large_block() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before_free = core.memory_info().free_pages;
        let page = core.alloc_pages(2).expect("alloc order=2 should succeed");
        let after_free = core.memory_info().free_pages;

        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        assert_eq!(unsafe { (*page).order }, 2);
        assert_eq!(after_free, before_free - 4);
        check_conservation(&core);

        unsafe { core.free_pages(&mut *page, 2) };
        let final_free = core.memory_info().free_pages;
        assert_eq!(final_free, before_free);
        check_conservation(&core);
    }

    #[test]
    fn alloc_returns_null_when_exhausted() {
        let mut mem = [0u8; 64 * 1024]; // 64 KiB = 16 pages
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + 64 * 1024;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        // Exhaust all available pages
        let mut allocated = Vec::new();
        while let Some(page) = core.alloc_pages(0) {
            allocated.push(unsafe { (*page).pfn });
        }

        // Next allocation should fail
        assert!(core.alloc_pages(0).is_none());

        // Free one and try again
        let pfn = allocated.pop().unwrap();
        let page = unsafe { &mut *core.page_at_mut(pfn) };
        unsafe { core.free_pages(page, 0) };
        assert!(core.alloc_pages(0).is_some());

        // Clean up remaining allocations
        for pfn in allocated {
            let page = unsafe { &mut *core.page_at_mut(pfn) };
            unsafe { core.free_pages(page, 0) };
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Split / coalesce
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod split_coalesce_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn split_on_demand() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        // Allocate order=1 (2 pages) — may trigger split from larger blocks
        let page = core.alloc_pages(1).expect("alloc order=1 should succeed");
        assert_eq!(unsafe { (*page).order }, 1);
        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        check_conservation(&core);

        unsafe { core.free_pages(&mut *page, 1) };
        check_conservation(&core);
    }

    #[test]
    fn coalesce_adjacent_buddies() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before = core.memory_info().free_pages;

        // Allocate two order=1 blocks that are buddies
        let p1 = core.alloc_pages(1).expect("first alloc");
        let p2 = core.alloc_pages(1).expect("second alloc");

        // Verify they are buddies (pfn differs by 2^1 = 2)
        let pfn1 = unsafe { (*p1).pfn };
        let pfn2 = unsafe { (*p2).pfn };
        assert_eq!(pfn1 ^ pfn2, 2, "allocated blocks should be buddies");

        // Free first buddy
        unsafe { core.free_pages(&mut *p1, 1) };
        let mid = core.memory_info().free_pages;
        assert_eq!(mid, before - 2);

        // Free second buddy — should coalesce to order=2
        unsafe { core.free_pages(&mut *p2, 1) };
        let after = core.memory_info().free_pages;
        assert_eq!(after, before);
        check_conservation(&core);
    }

    #[test]
    fn coalesce_chain() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before = core.memory_info().free_pages;

        // Allocate four order=0 pages that form two order=1 pairs
        let pages: Vec<_> = (0..4)
            .map(|_| core.alloc_pages(0).expect("alloc"))
            .collect();

        // Free all four in reverse order — should fully coalesce
        for page in pages.into_iter().rev() {
            unsafe { core.free_pages(&mut *page, 0) };
        }

        let after = core.memory_info().free_pages;
        assert_eq!(after, before);
        check_conservation(&core);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Aligned allocation
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod aligned_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn alloc_aligned_basic() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        // Allocate 8KB (order=1) aligned to 16KB (align_order=2)
        let page = core
            .alloc_pages_aligned(1, 2)
            .expect("aligned alloc should succeed");
        let addr = unsafe { core.pfn_to_phys((*page).pfn) };

        assert_eq!(
            addr & ((4 * PAGE_SIZE) - 1),
            0,
            "address should be 16KB aligned"
        );
        check_conservation(&core);

        unsafe { core.free_pages(&mut *page, 1) };
        check_conservation(&core);
    }

    #[test]
    fn alloc_aligned_does_not_leak() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before = core.memory_info().free_pages;

        // Multiple aligned allocations
        let mut allocated = Vec::new();
        for _ in 0..10 {
            if let Some(page) = core.alloc_pages_aligned(1, 2) {
                allocated.push(unsafe { (*page).pfn });
            }
        }

        // Free all
        for pfn in allocated {
            let page = unsafe { &mut *core.page_at_mut(pfn) };
            unsafe { core.free_pages(page, 1) };
        }

        let after = core.memory_info().free_pages;
        assert_eq!(after, before);
        check_conservation(&core);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Boundary tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod boundary_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn init_with_small_memory() {
        let mut mem = [0u8; 8 * 1024]; // 8 KiB = 2 pages
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + 8 * 1024;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let info = core.memory_info();
        // Most pages are reserved for metadata; may have 0 free pages
        check_conservation(&core);
    }

    #[test]
    fn alloc_max_order() {
        let mut mem = [0u8; 8 * 1024 * 1024]; // 8 MiB
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + 8 * 1024 * 1024;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        // Try allocating the largest possible order
        let page = core.alloc_pages(MAX_ORDER);
        if page.is_some() {
            let addr = unsafe { core.pfn_to_phys((*page.unwrap()).pfn) };
            assert_eq!(addr & ((PAGE_SIZE << MAX_ORDER) - 1), 0);
            unsafe { core.free_pages(&mut *page.unwrap(), MAX_ORDER) };
        }
        check_conservation(&core);
    }

    #[test]
    fn alloc_beyond_max_order_fails() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        assert!(core.alloc_pages(MAX_ORDER + 1).is_none());
    }

    #[test]
    fn alloc_zero_pages() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let page = core.alloc_pages(0);
        assert!(page.is_some());
        unsafe { core.free_pages(&mut *page.unwrap(), 0) };
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Stress / sequence tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod stress_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn random_alloc_free_sequence() {
        let mut mem = [0u8; 2 * 1024 * 1024]; // 2 MiB
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + 2 * 1024 * 1024;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before = core.memory_info().free_pages;

        let mut allocated: Vec<(usize, usize)> = Vec::new();
        let orders = [0, 0, 1, 0, 1, 2, 0, 1, 0, 2];

        for &order in &orders {
            if let Some(page) = core.alloc_pages(order) {
                let pfn = unsafe { (*page).pfn };
                allocated.push((pfn, order));
            }
        }

        // Free in reverse order
        for (pfn, order) in allocated.into_iter().rev() {
            let page = unsafe { &mut *core.page_at_mut(pfn) };
            unsafe { core.free_pages(page, order) };
        }

        let after = core.memory_info().free_pages;
        assert_eq!(after, before);
        check_conservation(&core);
    }

    #[test]
    fn alloc_free_alloc_no_leak() {
        let mut mem = [0u8; TEST_MEM_SIZE];
        let mem_start = mem.as_mut_ptr() as usize;
        let mem_end = mem_start + TEST_MEM_SIZE;

        let mut core = BuddyAllocatorCore::new();
        unsafe { core.init(mem_start, mem_end) };

        let before = core.memory_info().free_pages;

        // Allocate and free the same pattern multiple times
        for _ in 0..5 {
            let p1 = core.alloc_pages(2).unwrap();
            let p2 = core.alloc_pages(1).unwrap();
            unsafe { core.free_pages(&mut *p1, 2) };
            unsafe { core.free_pages(&mut *p2, 1) };
        }

        let after = core.memory_info().free_pages;
        assert_eq!(after, before);
        check_conservation(&core);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// order_of_size helper
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod order_tests {
    use super::super::{heap::order_of_size, page::PAGE_SIZE};
    use blueos_test_macro::test;

    #[test]
    fn order_of_size_basic() {
        assert_eq!(order_of_size(1), 0);
        assert_eq!(order_of_size(PAGE_SIZE), 0);
        assert_eq!(order_of_size(PAGE_SIZE + 1), 1);
        assert_eq!(order_of_size(2 * PAGE_SIZE), 1);
        assert_eq!(order_of_size(3 * PAGE_SIZE), 2);
        assert_eq!(order_of_size(4 * PAGE_SIZE), 2);
        assert_eq!(order_of_size(8 * PAGE_SIZE), 3);
        assert_eq!(order_of_size(16 * PAGE_SIZE), 4);
    }
}
