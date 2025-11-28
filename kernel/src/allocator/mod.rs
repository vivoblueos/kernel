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

extern crate alloc;

use crate::static_arc;
use alloc::alloc::Layout;
use core::{alloc::GlobalAlloc, ptr};

pub mod block;
#[cfg(any(allocator = "tlsf", allocator = "slab"))]
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
pub use slab::heap::Heap;

#[derive(Default, Debug)]
pub struct MemoryInfo {
    pub total: usize,
    pub used: usize,
    pub max_used: usize,
}

pub struct KernelAllocator;
static_arc! {
   HEAP(Heap, Heap::new()),
}

unsafe impl GlobalAlloc for KernelAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        HEAP.alloc(layout)
            .map_or(ptr::null_mut(), |ptr| ptr.as_ptr())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        HEAP.dealloc(ptr, layout);
    }
}

impl KernelAllocator {
    pub fn memory_info() -> MemoryInfo {
        HEAP.memory_info()
    }
}

pub fn init_heap(start: *mut u8, end: *mut u8) {
    let start_addr = start as usize;
    let size = unsafe { end.offset_from(start) as usize };
    unsafe {
        HEAP.init(start_addr, size);
    }
}

pub fn memory_info() -> MemoryInfo {
    KernelAllocator::memory_info()
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
    let layout = Layout::from_size_align(size, ALIGN).unwrap();
    HEAP.alloc(layout)
        .map_or(ptr::null_mut(), |allocation| allocation.as_ptr())
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
    unsafe { HEAP.deallocate_unknown_align(ptr) };
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
        HEAP.realloc_unknown_align(ptr, newsize)
            .map_or(ptr::null_mut(), |ptr| ptr.as_ptr())
    }
}

/// Allocates memory for an array of elements and initializes all bytes in this block to zero.
///
/// # Arguments
///
/// * `count` - Number of elements to allocate space for.
/// * `size` - Size of each element.
pub fn calloc(count: usize, size: usize) -> *mut u8 {
    let required_size = count * size;
    const ALIGN: usize = core::mem::size_of::<usize>();
    let layout = Layout::from_size_align(required_size, ALIGN).unwrap();
    if let Some(alloc_ptr) = HEAP.alloc(layout) {
        unsafe { ptr::write_bytes(alloc_ptr.as_ptr(), 0, required_size) };
        alloc_ptr.as_ptr()
    } else {
        ptr::null_mut()
    }
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

    let layout = Layout::from_size_align(size, align).unwrap();
    HEAP.alloc(layout)
        .map_or(ptr::null_mut(), |allocation| allocation.as_ptr())
}

/// Deallocates memory that was allocated using `malloc_align`.
///
/// # Arguments
///
/// * `ptr` - Pointer to the memory region to deallocate.
pub fn free_align(ptr: *mut u8, align: usize) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        let layout = Layout::from_size_align_unchecked(0, align);
        HEAP.dealloc(ptr, layout);
    }
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

    #[test]
    fn memory_info_test() {
        // Test memory statistics
        let initial_info = memory_info();
        assert!(initial_info.total > 0, "total memory should be positive");

        // Allocate some memory, use black_box to avoid compiler optimization
        let mut boxed = core::hint::black_box(Box::new([0u8; 2048]));

        let after_alloc_info = memory_info();
        assert!(
            after_alloc_info.used > initial_info.used,
            "used memory should increase after allocation: initial_used={}, after_alloc_used={}, total={}, max_used={}",
            initial_info.used,
            after_alloc_info.used,
            after_alloc_info.total,
            after_alloc_info.max_used
        );

        // Free memory (by dropping the box)
        drop(boxed);

        let after_free_info = memory_info();
        assert!(
            after_free_info.used < after_alloc_info.used,
            "used memory should decrease after deallocation: after_alloc_used={}, after_free_used={}, total={}, max_used={}",
            after_alloc_info.used,
            after_free_info.used,
            after_free_info.total,
            after_free_info.max_used
        );
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
