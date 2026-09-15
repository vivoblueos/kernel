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

//! Kernel wrapper for the raw buddy algorithm in `allocator_crate`.

mod heap;

use crate::types::{Arc, ArcInner};
pub(super) use allocator_crate::buddy::{order_of_size, PAGE_SIZE};
use heap::BuddyHeap;

#[allow(non_snake_case)]
mod BUDDY_ALLOC {
    use super::*;

    static CTRL_BLOCK: ArcInner<BuddyHeap> = ArcInner::new(BuddyHeap::new());
    pub(in crate::allocator) static PTR: Arc<BuddyHeap> =
        unsafe { Arc::from_static_inner_ref(&CTRL_BLOCK) };
}

pub(super) use BUDDY_ALLOC::PTR as BUDDY_ALLOC;

#[cfg(test)]
mod tests {
    use super::*;
    use allocator_crate::buddy::{BuddyAllocator, PAGE_SHIFT};
    use blueos_test_macro::test;
    use core::ptr::NonNull;

    #[repr(C, align(64))]
    struct TestMetadata([u8; 4096]);

    #[test]
    fn layout_reserves_complete_metadata_pages() {
        let phys_start = 0x4000_0000;
        let phys_end = phys_start + 64 * PAGE_SIZE;
        let kernel_end = phys_start + 2 * PAGE_SIZE + 123;
        let layout = heap::plan_layout(phys_start, phys_end, kernel_end, |addr| addr).unwrap();
        let metadata_layout = BuddyAllocator::metadata_layout(64).unwrap();

        assert_eq!(layout.metadata_virt_start, phys_start + 3 * PAGE_SIZE);
        assert_eq!(layout.metadata_len, metadata_layout.size());
        assert_eq!(layout.total_pages, 64);
        assert_eq!(
            layout.managed_start_pfn,
            3 + metadata_layout.size().div_ceil(PAGE_SIZE)
        );
    }

    #[test]
    fn wrapper_allocates_and_releases_physical_addresses() {
        // Keep the metadata buffer off the test thread's 4 KiB release stack.
        // Together with this function's call frames, an inline 4 KiB buffer
        // exceeds that stack and corrupts the adjacent static thread storage.
        let mut metadata = alloc::boxed::Box::new(TestMetadata([0; 4096]));
        let metadata_layout = BuddyAllocator::metadata_layout(64).unwrap();
        assert!(metadata_layout.size() <= metadata.0.len());
        let heap = BuddyHeap::new();
        unsafe {
            heap.init_for_test(
                0x8000_0000,
                64,
                4,
                NonNull::new(metadata.0.as_mut_ptr()).unwrap(),
                metadata.0.len(),
            )
            .unwrap();
        }

        let before = heap.memory_info();
        let phys = heap.alloc_pages_phys_addr(2).unwrap();
        assert_eq!(phys & ((PAGE_SIZE << 2) - 1), 0);
        assert_eq!(heap.phys_addr_to_pfn_for_test(phys), Some(4));
        assert_eq!(heap.memory_info().free_pages, before.free_pages - 4);
        unsafe { heap.free_pages_phys_addr(phys, 2) };
        assert_eq!(heap.memory_info(), before);

        assert_eq!(heap.phys_addr_to_pfn_for_test(phys + 1), None);
        assert_eq!(heap.phys_addr_to_pfn_for_test(0x7fff_f000), None);
        assert_eq!(
            heap.phys_addr_to_pfn_for_test(0x8000_0000 + (64 << PAGE_SHIFT)),
            None
        );
        assert_eq!(
            heap.phys_addr_to_virt_for_test(phys),
            crate::mm::kernel_phys_to_virt(phys)
        );
    }
}
