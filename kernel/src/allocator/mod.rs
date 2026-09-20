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

extern crate alloc;

use crate::{
    mm::{kernel_phys_to_virt, kernel_virt_to_phys},
    static_arc,
};
use alloc::alloc::Layout;
use core::{alloc::GlobalAlloc, ptr};

// Raw heap implementations are in the allocator_crate.
// This module only contains SpinLock wrappers and the GlobalAlloc impl.

#[cfg(allocator_buddy)]
mod buddy;
#[cfg(any(allocator = "tlsf", allocator = "slab", allocator = "slab_dynamic"))]
mod tlsf;
#[cfg(allocator = "tlsf")]
pub use tlsf::heap::Heap;

#[cfg(allocator = "llff")]
mod llff;
#[cfg(allocator = "llff")]
pub use llff::heap::LlffHeap as Heap;

#[cfg(allocator = "slab")]
mod slab;
#[cfg(allocator = "slab")]
use slab::heap::Heap;
#[cfg(allocator = "slab")]
pub use slab::heap::SlabHeap;

#[cfg(allocator = "slab_dynamic")]
mod slab;
#[cfg(allocator = "slab_dynamic")]
use slab::heap::DynamicSlabHeap as Heap;
#[cfg(allocator = "slab_dynamic")]
pub use slab::heap::DynamicSlabHeap;

pub use allocator_crate::MemoryInfo;

pub struct KernelAllocator;
static_arc! {
   HEAP(Heap, Heap::new()),
}

#[cfg(allocator_buddy)]
const BUDDY_THRESHOLD: usize = buddy::PAGE_SIZE / 2;

unsafe impl GlobalAlloc for KernelAllocator {
    // TODO: support slab requesting pages from buddy as memory pool
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        #[cfg(allocator_buddy)]
        {
            use buddy::order_of_size;
            let size = layout.size().max(layout.align());
            if size > BUDDY_THRESHOLD {
                let order = order_of_size(size);
                return buddy::BUDDY_ALLOC
                    .alloc_pages_phys_addr(order)
                    .map_or(ptr::null_mut(), |addr| kernel_phys_to_virt(addr) as *mut u8);
            }
        }
        HEAP.alloc(layout)
            .map_or(ptr::null_mut(), |ptr| ptr.as_ptr())
    }

    // TODO: support slab releasing pages back to buddy memory pool
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        #[cfg(allocator_buddy)]
        {
            use buddy::order_of_size;
            let size = layout.size().max(layout.align());
            if size > BUDDY_THRESHOLD {
                let order = order_of_size(size);
                let phys_addr = kernel_virt_to_phys(ptr as usize);
                buddy::BUDDY_ALLOC.free_pages_phys_addr(phys_addr, order);
                return;
            }
        }
        HEAP.dealloc(ptr, layout);
    }

    // TODO: support slab reallocating pages from buddy as memory pool
    unsafe fn realloc(&self, ptr: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
        #[cfg(allocator_buddy)]
        {
            let old_route_size = old_layout.size().max(old_layout.align());
            let new_route_size = new_size.max(old_layout.align());
            let old_is_buddy = old_route_size > BUDDY_THRESHOLD;
            let new_is_buddy = new_route_size > BUDDY_THRESHOLD;

            // Both sides stay on the small-object heap: try an in-place realloc.
            if !old_is_buddy && !new_is_buddy {
                return HEAP
                    .realloc(ptr, old_layout, new_size)
                    .map_or(ptr::null_mut(), |ptr| ptr.as_ptr());
            }
            // Both sides stay in the buddy pool: reuse the block when the
            // order (and thus the page count) is unchanged.
            if old_is_buddy
                && new_is_buddy
                && buddy::order_of_size(old_route_size) == buddy::order_of_size(new_route_size)
            {
                return ptr;
            }
            // Route changed, or buddy order changed: allocate a fresh block
            // via the routed `alloc`, copy the data over, then release the
            // old block via the routed `dealloc`. `self.alloc`/`self.dealloc`
            // dispatch on the size threshold, so this covers every
            // combination without special-casing slab vs. buddy.

            let Ok(new_layout) = Layout::from_size_align(new_size, old_layout.align()) else {
                return ptr::null_mut();
            };
            let new_ptr = self.alloc(new_layout);
            if new_ptr.is_null() {
                return ptr::null_mut();
            }
            ptr::copy_nonoverlapping(ptr, new_ptr, old_layout.size().min(new_size));
            self.dealloc(ptr, old_layout);
            new_ptr
        }

        #[cfg(not(allocator_buddy))]
        {
            HEAP.realloc(ptr, old_layout, new_size)
                .map_or(ptr::null_mut(), |ptr| ptr.as_ptr())
        }
    }
}

impl KernelAllocator {
    pub fn memory_info() -> MemoryInfo {
        HEAP.memory_info()
    }
}

/// Initialize the kernel heap.
///
/// # Two-Level Architecture (allocator_buddy enabled)
///
/// 1. **Level 1 — Physical page management**: The buddy allocator is
///    initialized with the full physical DRAM range. It manages all
///    physical pages via split/coalesce, providing page-aligned blocks
///    of power-of-two sizes.
///
/// 2. **Level 2 — Small-object allocation**: The slab allocator (or
///    tlsf/llff fallback) receives its page pool from the buddy allocator.
///    This keeps small-object allocation fast while physical memory is
///    centrally managed. The original `__heap_start..__heap_end` range
///    is used only as a fallback if buddy allocation fails.
///
/// # FDT / DTB Note
/// The physical memory range is currently hard-coded per board via
/// `PHYS_DRAM_BASE` and `PHYS_DRAM_SIZE`. This should be replaced with
/// FDT/DTB dynamic detection in a future update.
///
/// TODO: support slab initialization based on buddy allocator
pub fn init_heap(start: *mut u8, end: *mut u8) {
    #[cfg(allocator_buddy)]
    {
        // Level 1: Initialize buddy allocator to manage all physical memory.
        let phys_dram_base = crate::boards::PHYS_DRAM_BASE as usize;
        let phys_dram_size = crate::boards::PHYS_DRAM_SIZE as usize;
        unsafe {
            buddy::BUDDY_ALLOC.init(phys_dram_base, phys_dram_base + phys_dram_size);
        }

        // Level 2: Allocate page pool for small-object allocator from buddy.
        assert!(end > start);
        let pool_size = end as usize - start as usize;
        let order = buddy::order_of_size(pool_size);
        if let Some(pool_phys_addr) = buddy::BUDDY_ALLOC.alloc_pages_phys_addr(order) {
            unsafe {
                HEAP.init(kernel_phys_to_virt(pool_phys_addr), pool_size);
            }
        } else {
            // Fallback: use original heap range if buddy allocation fails.
            unsafe {
                HEAP.init(start as usize, pool_size);
            }
        }
    }

    #[cfg(not(allocator_buddy))]
    {
        let start_addr = start as usize;
        let size = unsafe { end.offset_from(start) as usize };
        unsafe {
            HEAP.init(start_addr, size);
        }
    }
}

pub fn memory_info() -> MemoryInfo {
    KernelAllocator::memory_info()
}

/// Metadata needed by the C-style allocation APIs, whose deallocation calls do
/// not carry the allocation size. The header lives immediately before the
/// pointer returned to the caller.
#[derive(Clone, Copy)]
struct AllocationHeader {
    size: usize,
    align: usize,
}

fn layout_with_header(layout: Layout) -> Option<(Layout, usize)> {
    Layout::new::<AllocationHeader>().extend(layout).ok()
}

/// Allocate through [`KernelAllocator`] while retaining enough information for
/// a later size-less [`free`] call.
unsafe fn alloc_with_header(layout: Layout) -> *mut u8 {
    let Some((allocation_layout, payload_offset)) = layout_with_header(layout) else {
        return ptr::null_mut();
    };
    let allocation = GlobalAlloc::alloc(&KernelAllocator, allocation_layout);
    if allocation.is_null() {
        return ptr::null_mut();
    }

    let payload = allocation.add(payload_offset);
    let header = payload
        .sub(core::mem::size_of::<AllocationHeader>())
        .cast::<AllocationHeader>();
    debug_assert_eq!(
        header.align_offset(core::mem::align_of::<AllocationHeader>()),
        0
    );
    header.write(AllocationHeader {
        size: layout.size(),
        align: layout.align(),
    });
    payload
}

/// Read the allocation header stored immediately before `ptr` and recover the
/// base pointer and layout passed to [`KernelAllocator`].
unsafe fn allocation_from_payload(ptr: *mut u8) -> (*mut u8, Layout, Layout) {
    let header = ptr
        .sub(core::mem::size_of::<AllocationHeader>())
        .cast::<AllocationHeader>()
        .read();
    let payload_layout = Layout::from_size_align_unchecked(header.size, header.align);
    let (allocation_layout, payload_offset) = layout_with_header(payload_layout)
        .expect("a previously allocated layout must remain valid");
    (ptr.sub(payload_offset), allocation_layout, payload_layout)
}

/// Allocate memory on heap and returns a pointer to it.
/// If size equals zero, then null mutable raw pointer will be returned.
// TODO: Make malloc a blocking API, i.e., if the heap lock is
// acquired by another thread, current thread should be suspended.
pub fn malloc(size: usize) -> *mut u8 {
    if core::intrinsics::unlikely(size == 0) {
        return ptr::null_mut();
    }
    const ALIGN: usize = core::mem::size_of::<usize>();
    let Ok(layout) = Layout::from_size_align(size, ALIGN) else {
        return ptr::null_mut();
    };
    unsafe { alloc_with_header(layout) }
}

/// Free previously allocated memory pointed by ptr.
///
/// # Arguments
///
/// * `ptr` - A pointer pointing to the memory location to be freed.
pub fn free(ptr: *mut u8) {
    if core::intrinsics::unlikely(ptr.is_null()) {
        return;
    }
    unsafe {
        let (allocation, layout, _) = allocation_from_payload(ptr);
        GlobalAlloc::dealloc(&KernelAllocator, allocation, layout);
    }
}

/// Reallocate memory pointed by ptr to have a new size.
///
/// # Arguments
///
/// * `ptr` - A pointer pointing to the memory location to be reallocated.
/// * `newsize` - The new size for the reallocated memory.
pub fn realloc(ptr: *mut u8, newsize: usize) -> *mut u8 {
    if newsize == 0 {
        free(ptr);
        return ptr::null_mut();
    }
    if ptr.is_null() {
        return malloc(newsize);
    }
    unsafe {
        let (allocation, old_allocation_layout, old_payload_layout) = allocation_from_payload(ptr);
        let Ok(new_payload_layout) = Layout::from_size_align(newsize, old_payload_layout.align())
        else {
            return ptr::null_mut();
        };
        let Some((new_allocation_layout, new_payload_offset)) =
            layout_with_header(new_payload_layout)
        else {
            return ptr::null_mut();
        };
        let (_, old_payload_offset) = layout_with_header(old_payload_layout)
            .expect("a previously allocated layout must remain valid");
        debug_assert_eq!(new_payload_offset, old_payload_offset);

        let new_allocation = GlobalAlloc::realloc(
            &KernelAllocator,
            allocation,
            old_allocation_layout,
            new_allocation_layout.size(),
        );
        if new_allocation.is_null() {
            return ptr::null_mut();
        }

        let new_payload = new_allocation.add(new_payload_offset);
        new_payload
            .sub(core::mem::size_of::<AllocationHeader>())
            .cast::<AllocationHeader>()
            .write(AllocationHeader {
                size: newsize,
                align: new_payload_layout.align(),
            });
        new_payload
    }
}

/// Allocates memory for an array of elements and initializes all bytes in this block to zero.
///
/// # Arguments
///
/// * `count` - Number of elements to allocate space for.
/// * `size` - Size of each element.
pub fn calloc(count: usize, size: usize) -> *mut u8 {
    let Some(required_size) = count.checked_mul(size) else {
        return ptr::null_mut();
    };
    let allocation = malloc(required_size);
    if !allocation.is_null() {
        unsafe { ptr::write_bytes(allocation, 0, required_size) };
    }
    allocation
}

/// Allocates aligned memory of at least the specified size.
///
/// # Arguments
///
/// * `size` - Minimum size of the memory region to allocate.
/// * `align` - Alignment requirement for the returned memory.
pub fn malloc_align(size: usize, align: usize) -> *mut u8 {
    if core::intrinsics::unlikely(size == 0) {
        return ptr::null_mut();
    }

    let Ok(layout) = Layout::from_size_align(size, align) else {
        return ptr::null_mut();
    };
    unsafe { alloc_with_header(layout) }
}

/// Deallocates memory that was allocated using `malloc_align`.
///
/// # Arguments
///
/// * `ptr` - Pointer to the memory region to deallocate.
pub fn free_align(ptr: *mut u8, _align: usize) {
    free(ptr);
}

pub(crate) fn get_max_free_block_size() -> usize {
    unsafe { HEAP.get_max_free_block_size() }
}

/// Returns the offset of the address within the alignment.
///
/// Equivalent to `addr % align`, but the alignment must be a power of two.
#[inline]
pub const fn align_offset(addr: usize, align: usize) -> usize {
    addr & (align - 1)
}

/// Checks whether the address has the demanded alignment.
///
/// Equivalent to `addr % align == 0`, but the alignment must be a power of two.
#[inline]
pub const fn is_aligned(addr: usize, align: usize) -> bool {
    align_offset(addr, align) == 0
}

#[cfg(allocator = "slab_dynamic")]
pub fn check_slab_memory_pressure() {
    unsafe { HEAP.check_memory_pressure() };
}

#[cfg(any(allocator = "slab", allocator = "slab_dynamic"))]
pub fn print_slab_stat() {
    unsafe { HEAP.print_slab_stat() };
}

#[cfg(allocator = "slab_dynamic")]
pub fn reclaim_page_pool() {
    unsafe { HEAP.reclaim_page_pool() };
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{alloc::Layout, boxed::Box, vec, vec::Vec};
    use blueos_test_macro::test;

    #[test]
    fn max_free_block_comprehensive() {
        // Test 1: Basic behavior - check max free block after pool initialization
        let max_free = get_max_free_block_size();
        assert!(
            max_free > 0,
            "max free block should be positive after pool insert"
        );

        // Max free block decreases on allocation
        let _boxed = Box::new([0u8; 1024 * 64]);
        let after = get_max_free_block_size();
        assert!(
            after <= max_free,
            "max free block should decrease after allocation"
        );
    }

    #[test]
    fn basic_allocation_and_deallocation() {
        // Test basic allocation and deallocation
        let mut boxed = Box::new([0u8; 1024]);

        // Write some data to verify the memory is usable
        boxed[0] = 0xAA;
        // Verify first byte is written correctly
        assert_eq!(boxed[0], 0xAAu8);
    }

    #[test]
    fn multiple_allocations() {
        // Test multiple allocations of different sizes
        let sizes = [64, 128, 256, 512];

        let mut boxes = Vec::new();
        for size in &sizes {
            let boxed = Box::new(vec![0u8; *size]);
            boxes.push(boxed);
        }

        // Boxes are automatically deallocated when they go out of scope
    }

    #[test]
    fn alignment_test() {
        // Test allocations with different alignment requirements
        // Box automatically handles alignment, but we can verify it works
        let alignments = [4, 8, 16, 32, 64, 128];

        for align in alignments {
            // Use alloc::alloc::alloc to test alignment
            let layout = Layout::from_size_align(256, align).unwrap();
            let ptr = unsafe { alloc::alloc::alloc(layout) };
            assert!(
                !ptr.is_null(),
                "allocation with align {} should succeed",
                align
            );

            // Verify alignment
            assert_eq!(
                ptr as usize % align,
                0,
                "pointer should be aligned to {} bytes",
                align
            );

            // Free the memory
            unsafe { alloc::alloc::dealloc(ptr, layout) };
        }
    }

    #[test]
    fn c_style_allocation_apis_preserve_layout_metadata() {
        unsafe {
            let ptr = malloc(257);
            assert!(!ptr.is_null());
            assert_eq!(ptr as usize & (core::mem::size_of::<usize>() - 1), 0);
            for offset in 0..257 {
                ptr.add(offset).write((offset as u8).wrapping_mul(17));
            }
            for offset in 0..257 {
                assert_eq!(ptr.add(offset).read(), (offset as u8).wrapping_mul(17));
            }
            free(ptr);

            let aligned = malloc_align(257, 256);
            assert!(!aligned.is_null());
            assert_eq!(aligned as usize & 255, 0);
            aligned.write(0x5A);
            aligned.add(256).write(0xA5);
            assert_eq!(aligned.read(), 0x5A);
            assert_eq!(aligned.add(256).read(), 0xA5);
            // `free` is also the deallocator used by the `free_mem` syscall
            // for memory returned from `malloc_align`.
            free(aligned);

            let aligned = malloc_align(33, 64);
            assert!(!aligned.is_null());
            free_align(aligned, 64);
        }
    }

    #[test]
    fn calloc_zeroes_memory_and_rejects_overflow() {
        unsafe {
            let ptr = calloc(37, 11);
            assert!(!ptr.is_null());
            for offset in 0..37 * 11 {
                assert_eq!(ptr.add(offset).read(), 0);
            }
            free(ptr);
        }
        assert!(calloc(usize::MAX, 2).is_null());
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn c_style_realloc_crosses_allocator_routes() {
        const SMALL_SIZE: usize = 128;
        const LARGE_SIZE: usize = BUDDY_THRESHOLD + 1;

        unsafe {
            let small = malloc(SMALL_SIZE);
            assert!(!small.is_null());
            for offset in 0..SMALL_SIZE {
                small.add(offset).write((offset as u8).wrapping_mul(31));
            }

            let large = realloc(small, LARGE_SIZE);
            assert!(!large.is_null());
            for offset in 0..SMALL_SIZE {
                assert_eq!(large.add(offset).read(), (offset as u8).wrapping_mul(31));
            }
            large.add(LARGE_SIZE - 1).write(0xC3);

            let small_again = realloc(large, SMALL_SIZE / 2);
            assert!(!small_again.is_null());
            for offset in 0..SMALL_SIZE / 2 {
                assert_eq!(
                    small_again.add(offset).read(),
                    (offset as u8).wrapping_mul(31)
                );
            }
            free(small_again);
        }
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn c_style_realloc_failure_keeps_old_allocation() {
        unsafe {
            let ptr = malloc(64);
            assert!(!ptr.is_null());
            ptr.write(0x6D);

            assert!(realloc(ptr, usize::MAX).is_null());
            assert_eq!(ptr.read(), 0x6D);
            free(ptr);
        }
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn c_style_page_alignment_routes_through_buddy() {
        unsafe {
            let ptr = malloc_align(64, buddy::PAGE_SIZE);
            assert!(!ptr.is_null());
            assert_eq!(ptr as usize & (buddy::PAGE_SIZE - 1), 0);
            ptr.write(0x3C);
            ptr.add(63).write(0xC3);
            assert_eq!(ptr.read(), 0x3C);
            assert_eq!(ptr.add(63).read(), 0xC3);
            free_align(ptr, buddy::PAGE_SIZE);
        }
    }

    #[test]
    fn coalescing_test() {
        // Test that adjacent blocks can be coalesced
        // Allocate two blocks
        let boxed1 = Box::new([0u8; 1024]);
        let boxed2 = Box::new([0u8; 1024]);

        // Free both blocks (by dropping them)
        drop(boxed1);
        drop(boxed2);

        // Try to allocate a larger block that should fit after coalescing
        let _large_boxed = Box::new([0u8; 2048]);
    }

    #[test]
    fn realloc_test() {
        // Test reallocation functionality using allocator::realloc
        let initial_size = 512;
        let mut boxed = Box::new(vec![0x42u8; initial_size]);

        // Reallocate to larger size
        let new_size = 1024;
        boxed.resize(new_size, 0);

        // Verify data is preserved (at least the original part)
        assert_eq!(boxed[0], 0x42u8);

        // Reallocate to smaller size
        let smaller_size = 256;
        boxed.resize(smaller_size, 0);
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn realloc_crosses_buddy_threshold() {
        let small_layout = Layout::from_size_align(2048, core::mem::size_of::<usize>()).unwrap();
        let large_layout = Layout::from_size_align(2049, core::mem::size_of::<usize>()).unwrap();

        unsafe {
            let ptr = alloc::alloc::alloc(small_layout);
            assert!(!ptr.is_null(), "small allocation should succeed");
            for offset in 0..small_layout.size() {
                ptr.add(offset).write((offset as u8).wrapping_mul(13));
            }

            let ptr = alloc::alloc::realloc(ptr, small_layout, large_layout.size());
            assert!(
                !ptr.is_null(),
                "realloc across buddy threshold should succeed"
            );
            for offset in 0..small_layout.size() {
                assert_eq!(ptr.add(offset).read(), (offset as u8).wrapping_mul(13));
            }
            ptr.add(large_layout.size() - 1).write(0xA5);
            assert_eq!(ptr.add(large_layout.size() - 1).read(), 0xA5);

            alloc::alloc::dealloc(ptr, large_layout);
        }
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn realloc_shrinks_below_buddy_threshold() {
        let large_layout = Layout::from_size_align(2049, core::mem::size_of::<usize>()).unwrap();
        let small_layout = Layout::from_size_align(2048, core::mem::size_of::<usize>()).unwrap();

        unsafe {
            let ptr = alloc::alloc::alloc(large_layout);
            assert!(!ptr.is_null(), "large allocation should succeed");
            for offset in 0..small_layout.size() {
                ptr.add(offset).write((offset as u8).wrapping_mul(29));
            }

            let ptr = alloc::alloc::realloc(ptr, large_layout, small_layout.size());
            assert!(
                !ptr.is_null(),
                "realloc below buddy threshold should succeed"
            );
            for offset in 0..small_layout.size() {
                assert_eq!(ptr.add(offset).read(), (offset as u8).wrapping_mul(29));
            }
            ptr.add(small_layout.size() - 1).write(0x3C);
            assert_eq!(ptr.add(small_layout.size() - 1).read(), 0x3C);

            alloc::alloc::dealloc(ptr, small_layout);
        }
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn buddy_routing_uses_both_size_and_alignment() {
        let heap_layout = Layout::from_size_align(BUDDY_THRESHOLD, 8).unwrap();
        let buddy_layout = Layout::from_size_align(BUDDY_THRESHOLD + 1, 8).unwrap();
        let aligned_layout = Layout::from_size_align(1, buddy::PAGE_SIZE).unwrap();

        unsafe {
            let heap_ptr = GlobalAlloc::alloc(&KernelAllocator, heap_layout);
            assert!(!heap_ptr.is_null());
            heap_ptr.write(0x11);
            assert_eq!(heap_ptr.read(), 0x11);

            let buddy_ptr = GlobalAlloc::alloc(&KernelAllocator, buddy_layout);
            assert!(!buddy_ptr.is_null());
            assert_eq!(buddy_ptr as usize & (buddy::PAGE_SIZE - 1), 0);
            buddy_ptr.write(0x22);
            buddy_ptr.add(buddy_layout.size() - 1).write(0x23);

            let aligned_ptr = GlobalAlloc::alloc(&KernelAllocator, aligned_layout);
            assert!(!aligned_ptr.is_null());
            assert_eq!(aligned_ptr as usize & (buddy::PAGE_SIZE - 1), 0);
            aligned_ptr.write(0x33);

            assert!((buddy_ptr as usize).abs_diff(aligned_ptr as usize) >= buddy::PAGE_SIZE);
            assert_eq!(buddy_ptr.read(), 0x22);
            assert_eq!(buddy_ptr.add(buddy_layout.size() - 1).read(), 0x23);
            assert_eq!(aligned_ptr.read(), 0x33);

            GlobalAlloc::dealloc(&KernelAllocator, aligned_ptr, aligned_layout);
            GlobalAlloc::dealloc(&KernelAllocator, buddy_ptr, buddy_layout);
            GlobalAlloc::dealloc(&KernelAllocator, heap_ptr, heap_layout);
        }
    }

    #[cfg(allocator_buddy)]
    #[test]
    fn failed_cross_threshold_realloc_keeps_old_block_valid() {
        let old_layout = Layout::from_size_align(128, core::mem::size_of::<usize>()).unwrap();
        unsafe {
            let old_ptr = GlobalAlloc::alloc(&KernelAllocator, old_layout);
            assert!(!old_ptr.is_null());
            old_ptr.write(0x6D);

            let new_ptr = GlobalAlloc::realloc(&KernelAllocator, old_ptr, old_layout, usize::MAX);
            assert!(new_ptr.is_null());
            assert_eq!(old_ptr.read(), 0x6D);

            GlobalAlloc::dealloc(&KernelAllocator, old_ptr, old_layout);
        }
    }

    #[test]
    fn fragmentation_test() {
        // Test memory fragmentation handling
        let mut boxes = Vec::new();

        // Allocate many small blocks
        for _ in 0..50 {
            let boxed = Box::new([0u8; 64]);
            boxes.push(Some(boxed));
        }

        // Free every other block to create fragmentation
        for i in (0..boxes.len()).step_by(2) {
            boxes[i] = None;
        }

        // Try to allocate a larger block
        let _large_boxed = Box::new([0u8; 512]);

        // Clean up remaining blocks
        for i in (1..boxes.len()).step_by(2) {
            boxes[i] = None;
        }
    }

    #[test]
    fn zero_sized_allocation() {
        // Test zero-sized allocation
        // Box doesn't support zero-sized arrays, so we use a unit type
        let _boxed: Box<()> = Box::new(());
        // Zero-sized allocations are handled automatically
    }

    #[test]
    fn size_of_allocation_test() {
        // Test getting the size of an allocation
        const REQUESTED_SIZE: usize = 1024;
        let boxed = Box::new([0u8; REQUESTED_SIZE]);

        // Get actual allocation size (may be larger due to alignment and overhead)
        // Note: size_of_allocation is a method on Heap, not a module function
        // We can verify the allocation worked by checking the pointer is valid
        assert_eq!(boxed.len(), REQUESTED_SIZE, "allocation should succeed");
    }
}
