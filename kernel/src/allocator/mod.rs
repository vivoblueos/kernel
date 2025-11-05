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
    pub fn memory_info(&self) -> MemoryInfo {
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

#[derive(Default, Debug)]
pub struct MemoryInfo {
    pub total: usize,
    pub used: usize,
    pub max_used: usize,
}

pub fn memory_info() -> MemoryInfo {
    HEAP.memory_info()
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

