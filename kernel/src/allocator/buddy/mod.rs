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

use self::{
    heap::{order_of_size, BuddyMemoryInfo},
    page::{PageFlags, MAX_ORDER, PAGE_SIZE},
};
use crate::types::{Arc, ArcInner};
use alloc::vec::Vec;
use core::{mem, ptr, sync::atomic::Ordering};

pub mod heap;
pub mod page;

use heap::BuddyAllocator;

// Physical memory layout of buddy allocator
// ============================================================================
//
//   mem_start (e.g. 0x4000_0000)
//   +-- kernel image (.text .rodata .data .bss)
//   +-- __heap_start -- __heap_end (a small memory region reserved by link.x)
//   |
//   |    +--------------------------------------------------------------+
//   |    |  struct Page[total_pages]  <-- page descriptor array         |
//   |    |  each page 32-48 bytes, flags: FREE/RESERVED/order/refcount  |
//   |    +--------------------------------------------------------------+
//   |
//   +--> start_pfn (first usable page after metadata)
//        |
//        |  Usable region is split into the largest possible buddy-aligned
//        |  blocks (up to MAX_ORDER=11, 8 MB). The head page of each block
//        |  has FREE=1 and its actual order; all other pages have FREE=0
//        |  (invalid). The first block's order may be < MAX_ORDER if
//        |  start_pfn is not aligned to a MAX_ORDER boundary.
//        |
//        |  +----------+  +----------+         +----------+  +----------+
//        |  | pfn=N    |  | pfn=N+1  |  ...    | pfn=M    |  | pfn=M+1  |  ...
//        |  | FREE=1   |  | FREE=0   |         | FREE=1   |  | FREE=0   |
//        |  | order=11 |  | (invalid)|         | order=11 |  | (invalid)|
//        |  +----------+  +----------+         +----------+  +----------+
//        |       ^ chunk 0 head                     ^ chunk 1 head
//        |
//        |           ... all pages in between FREE=0 ...
//        |
//        |  +----------+         +----------+
//        |  | pfn=P    |  ...    | pfn=end  |
//        |  | FREE=1   |         | FREE=0   |
//        |  | order=K  |         | (invalid)|
//        |  +----------+         +----------+
//        |       ^ last chunk head (order=K < 11 if size < 8 MB)
//        |
//        +--> each MAX_ORDER chunk spans 2048 pages; only the head page
//             has valid flags.
//
//   mem_end (e.g. 0x4800_0000)
// ============================================================================

#[allow(non_snake_case)]
mod BUDDY_ALLOC {
    use super::*;

    // ArcInner contains heap memory (BuddyAllocator) and a reference count, this is an immutable reference
    static CTRL_BLOCK: ArcInner<BuddyAllocator> = ArcInner::new(BuddyAllocator::new());
    // Wrap ArcInner with Arc to form a globally accessible Arc<BuddyAllocator>, initialized at compile time
    pub(in crate::allocator) static PTR: Arc<BuddyAllocator> =
        unsafe { Arc::from_static_inner_ref(&CTRL_BLOCK) };
}

// Expose BUDDY_ALLOC's PTR as BUDDY_ALLOC so other modules can access the global BuddyAllocator instance via allocator::buddy::BUDDY_ALLOC.
pub(super) use BUDDY_ALLOC::PTR as BUDDY_ALLOC;

#[cfg(test)]
fn assert_page_conservation() {
    let info = BUDDY_ALLOC.memory_info();
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

#[cfg(test)]
macro_rules! buddy_test_exclusive {
    () => {
        let _buddy_test_guard = BUDDY_ALLOC.test_exclusive();
    };
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
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        let info = BUDDY_ALLOC.memory_info();
        assert!(info.total_pages > 0);
        assert!(info.reserved_pages > 0);
        assert_page_conservation();
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
    }

    #[test]
    fn alloc_single_page() {
        buddy_test_exclusive!();
        let before_free = BUDDY_ALLOC.memory_info().free_pages;
        let page = BUDDY_ALLOC
            .alloc_pages(0)
            .expect("alloc single page should succeed");
        let after_free = BUDDY_ALLOC.memory_info().free_pages;

        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        assert_eq!(unsafe { (*page).order }, 0);
        assert_eq!(after_free, before_free - 1);
        assert_page_conservation();

        unsafe { BUDDY_ALLOC.free_pages(&mut *page, 0) };
        let final_free = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(final_free, before_free);
        assert_page_conservation();
    }

    #[test]
    fn alloc_large_block() {
        buddy_test_exclusive!();
        let before_free = BUDDY_ALLOC.memory_info().free_pages;
        let page = BUDDY_ALLOC
            .alloc_pages(2)
            .expect("alloc order=2 should succeed");
        let after_free = BUDDY_ALLOC.memory_info().free_pages;

        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        assert_eq!(unsafe { (*page).order }, 2);
        assert_eq!(after_free, before_free - 4);
        assert_page_conservation();

        unsafe { BUDDY_ALLOC.free_pages(&mut *page, 2) };
        let final_free = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(final_free, before_free);
        assert_page_conservation();
    }

    #[test]
    fn alloc_returns_null_when_exhausted() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        let mut allocated = Vec::new();
        // Exhaust all available pages
        while let Some(page) = BUDDY_ALLOC.alloc_pages(0) {
            allocated.push(unsafe { (*page).pfn });
        }

        // Next allocation should fail
        assert!(BUDDY_ALLOC.alloc_pages(0).is_none());

        // Free one and try again
        let pfn = allocated.pop().unwrap();
        let page = unsafe { &mut *BUDDY_ALLOC.pfn_to_virt(pfn) };
        unsafe { BUDDY_ALLOC.free_pages(page, 0) };
        let recovered = BUDDY_ALLOC
            .alloc_pages(0)
            .expect("should succeed after free");
        unsafe { BUDDY_ALLOC.free_pages(&mut *recovered, 0) };

        // Clean up remaining allocations
        for pfn in allocated.drain(..) {
            let page = unsafe { &mut *BUDDY_ALLOC.pfn_to_virt(pfn) };
            unsafe { BUDDY_ALLOC.free_pages(page, 0) };
        }
        // allocated is now empty; shrink_to_fit releases the backing heap memory
        allocated.shrink_to_fit();
        mem::drop(allocated);

        let after = BUDDY_ALLOC.memory_info().free_pages;

        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn test_exclusive_guard_is_reentrant_for_owner() {
        let _outer_guard = BUDDY_ALLOC.test_exclusive();
        let _inner_guard = BUDDY_ALLOC.test_exclusive();

        let before = BUDDY_ALLOC.memory_info().free_pages;
        let page = BUDDY_ALLOC
            .alloc_pages(0)
            .expect("owner should allocate while holding nested guards");

        unsafe { BUDDY_ALLOC.free_pages(&mut *page, 0) };

        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
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
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        // Allocate order=1 (2 pages) — may trigger split from larger blocks
        let page = BUDDY_ALLOC
            .alloc_pages(1)
            .expect("alloc order=1 should succeed");
        assert_eq!(unsafe { (*page).order }, 1);
        assert!(!unsafe { (*page).flags.contains(PageFlags::FREE) });
        assert_page_conservation();

        unsafe { BUDDY_ALLOC.free_pages(&mut *page, 1) };
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn coalesce_adjacent_buddies() {
        buddy_test_exclusive!();
        let total_free = BUDDY_ALLOC.memory_info().free_pages;
        let mut allocated = Vec::new();
        let mut buddies = None;

        // Keep allocating pages until we find two pages whose PFNs are buddies of each other.
        while let Some(page) = BUDDY_ALLOC.alloc_pages(1) {
            let pfn = unsafe { (*page).pfn };
            if let Some(index) = allocated
                .iter()
                .position(|&(allocated_pfn, _)| allocated_pfn ^ pfn == 2)
            {
                let (buddy_pfn, buddy_page) = allocated.swap_remove(index);
                buddies = Some((buddy_pfn, buddy_page, pfn, page));
                break;
            }
            allocated.push((pfn, page));
        }

        // Free the extra pages that were allocated earlier
        for (_, page) in allocated {
            unsafe { BUDDY_ALLOC.free_pages(&mut *page, 1) };
        }

        let (pfn1, p1, pfn2, p2) = buddies.expect("must find order=1 buddy pair");
        let before = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(before, total_free - 4);

        unsafe { BUDDY_ALLOC.free_pages(&mut *p1, 1) };
        let mid = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(mid, total_free - 2);

        unsafe { BUDDY_ALLOC.free_pages(&mut *p2, 1) };
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, total_free);

        // The two order=1 buddies should have coalesced into a single larger
        // block (order >= 2, possibly merged further with neighboring free
        // buddies). Verify coalescing directly via the page descriptors without
        // relying on any particular free-list ordering: after the merge, the two
        // original buddy heads can no longer BOTH remain free order=1 blocks.
        let head1 = unsafe { &*BUDDY_ALLOC.pfn_to_virt(pfn1) };
        let head2 = unsafe { &*BUDDY_ALLOC.pfn_to_virt(pfn2) };
        let both_still_order1_free = head1.flags.contains(PageFlags::FREE)
            && head1.order == 1
            && head2.flags.contains(PageFlags::FREE)
            && head2.order == 1;
        assert!(
            !both_still_order1_free,
            "buddies pfn={} and pfn={} did not coalesce (both still free order=1 heads)",
            pfn1, pfn2
        );

        // The coalesced block is now available, so an order=2 allocation must
        // succeed. Its pfn is not asserted: under FIFO free lists the block
        // returned need not be the one just coalesced.
        let merged = BUDDY_ALLOC
            .alloc_pages(2)
            .expect("order=2 alloc after coalescing");
        unsafe { BUDDY_ALLOC.free_pages(&mut *merged, 2) };
        assert_page_conservation();
    }

    #[test]
    fn coalesce_chain() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;

        // Allocate four order=0 pages that form two order=1 pairs
        let pages: Vec<_> = (0..4)
            .map(|_| BUDDY_ALLOC.alloc_pages(0).expect("alloc"))
            .collect();

        // Free all four in reverse order — should fully coalesce
        for page in pages.into_iter().rev() {
            unsafe { BUDDY_ALLOC.free_pages(&mut *page, 0) };
        }

        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn coalescing_clears_removed_buddy_head_metadata() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        let p1 = BUDDY_ALLOC.alloc_pages(0).expect("first page");
        let p2 = BUDDY_ALLOC.alloc_pages(0).expect("second page");
        let p1_pfn = unsafe { (*p1).pfn };
        let p2_pfn = unsafe { (*p2).pfn };

        // They are not buddy pairs
        if p1_pfn ^ p2_pfn != 1 {
            unsafe { BUDDY_ALLOC.free_pages(&mut *p1, 0) };
            unsafe { BUDDY_ALLOC.free_pages(&mut *p2, 0) };
            let after = BUDDY_ALLOC.memory_info().free_pages;
            assert_eq!(after, before);
            return;
        }

        // They are buddy pairs
        unsafe { BUDDY_ALLOC.free_pages(&mut *p1, 0) };
        unsafe { BUDDY_ALLOC.free_pages(&mut *p2, 0) };

        let removed_buddy_pfn = p1_pfn.max(p2_pfn);
        let removed_buddy = unsafe { &*BUDDY_ALLOC.pfn_to_virt(removed_buddy_pfn) };
        assert!(
            !removed_buddy.flags.contains(PageFlags::FREE),
            "merged buddy head pfn={} must not remain marked free",
            removed_buddy_pfn
        );
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
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
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        // Allocate 8KB (order=1) aligned to 16KB (align_order=2)
        let page = BUDDY_ALLOC
            .alloc_pages_aligned(1, 2)
            .expect("aligned alloc should succeed");
        let addr = unsafe { BUDDY_ALLOC.pfn_to_phys((*page).pfn) };

        assert_eq!(
            addr & ((4 * PAGE_SIZE) - 1),
            0,
            "address should be 16KB aligned"
        );
        assert_page_conservation();

        unsafe { BUDDY_ALLOC.free_pages(&mut *page, 1) };
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn alloc_aligned_does_not_leak() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        let mut allocated = Vec::new();
        // Multiple aligned allocations
        for _ in 0..10 {
            if let Some(page) = BUDDY_ALLOC.alloc_pages_aligned(1, 2) {
                allocated.push(unsafe { (*page).pfn });
            }
        }

        // Free all
        for pfn in allocated.drain(..) {
            let page = unsafe { &mut *BUDDY_ALLOC.pfn_to_virt(pfn) };
            unsafe { BUDDY_ALLOC.free_pages(page, 1) };
        }
        allocated.shrink_to_fit();
        mem::drop(allocated);

        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
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
    fn alloc_max_order() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        // Try allocating the largest possible order
        let page = BUDDY_ALLOC.alloc_pages(MAX_ORDER);
        if page.is_some() {
            let addr = unsafe { BUDDY_ALLOC.pfn_to_phys((*page.unwrap()).pfn) };
            assert_eq!(addr & ((PAGE_SIZE << MAX_ORDER) - 1), 0);
            unsafe { BUDDY_ALLOC.free_pages(&mut *page.unwrap(), MAX_ORDER) };
        }
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn alloc_beyond_max_order_fails() {
        buddy_test_exclusive!();
        assert!(BUDDY_ALLOC.alloc_pages(MAX_ORDER + 1).is_none());
    }

    #[test]
    fn alloc_zero_pages() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;
        let page = BUDDY_ALLOC.alloc_pages(0);
        assert!(page.is_some());
        unsafe { BUDDY_ALLOC.free_pages(&mut *page.unwrap(), 0) };
        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
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
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;

        let mut allocated: Vec<(usize, usize)> = Vec::new();
        let orders = [0, 0, 1, 0, 1, 2, 0, 1, 0, 2];

        for &order in &orders {
            if let Some(page) = BUDDY_ALLOC.alloc_pages(order) {
                let pfn = unsafe { (*page).pfn };
                allocated.push((pfn, order));
            }
        }

        // Free in reverse order
        for (pfn, order) in allocated.into_iter().rev() {
            let page = unsafe { &mut *BUDDY_ALLOC.pfn_to_virt(pfn) };
            unsafe { BUDDY_ALLOC.free_pages(page, order) };
        }

        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }

    #[test]
    fn alloc_free_alloc_no_leak() {
        buddy_test_exclusive!();
        let before = BUDDY_ALLOC.memory_info().free_pages;

        // Allocate and free the same pattern multiple times
        for _ in 0..5 {
            let p1 = BUDDY_ALLOC.alloc_pages(2).unwrap();
            let p2 = BUDDY_ALLOC.alloc_pages(1).unwrap();
            unsafe { BUDDY_ALLOC.free_pages(&mut *p1, 2) };
            unsafe { BUDDY_ALLOC.free_pages(&mut *p2, 1) };
        }

        let after = BUDDY_ALLOC.memory_info().free_pages;
        assert_eq!(after, before);
        assert_page_conservation();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// order_of_size helper
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod order_tests {
    use super::{heap::order_of_size, page::PAGE_SIZE};
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
