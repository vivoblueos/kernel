#![no_std]
#![allow(internal_features)]
#![feature(core_intrinsics)]
#![feature(const_trait_impl)]

extern crate alloc;

use alloc::alloc::Layout;
use core::{alloc::GlobalAlloc, ptr};

pub(crate) mod block;
pub mod sync;
pub mod support;

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

#[macro_export]
macro_rules! kprintln {
    ($fmt:expr) => {};
    ($fmt:expr, $($arg:tt)*) => {};
}

// A simplified static-arc that wraps a value in a static reference.
// This replaces the original `static_arc!` macro from the kernel.
#[macro_export]
macro_rules! static_arc {
    ($name:ident($ty:ty, $val:expr),) => {
        #[allow(non_snake_case)]
        mod $name {
            use super::*;
            static INNER: $ty = $val;
            pub(super) static PTR: &$ty = &INNER;
        }
        #[allow(unused_imports)]
        use $name::PTR as $name;
    };
}

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

    unsafe fn realloc(&self, ptr: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
        HEAP.realloc(ptr, old_layout, new_size)
            .map_or(ptr::null_mut(), |ptr| ptr.as_ptr())
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
pub fn free(ptr: *mut u8) {
    if core::intrinsics::unlikely(ptr.is_null()) {
        return;
    }
    unsafe { HEAP.deallocate_unknown_align(ptr) };
}

/// Reallocate memory pointed by ptr to have a new size.
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
pub fn calloc(count: usize, size: usize) -> *mut u8 {
    let required_size = count * size;
    const ALIGN: usize = core::mem::size_of::<usize>();
    if let Ok(layout) = Layout::from_size_align(required_size, ALIGN) {
        if let Some(alloc_ptr) = HEAP.alloc(layout) {
            unsafe { ptr::write_bytes(alloc_ptr.as_ptr(), 0, required_size) };
            alloc_ptr.as_ptr()
        } else {
            ptr::null_mut()
        }
    } else {
        ptr::null_mut()
    }
}

/// Allocates aligned memory of at least the specified size.
pub fn malloc_align(size: usize, align: usize) -> *mut u8 {
    if core::intrinsics::unlikely(size == 0) {
        return ptr::null_mut();
    }

    let layout = Layout::from_size_align(size, align).unwrap();
    HEAP.alloc(layout)
        .map_or(ptr::null_mut(), |allocation| allocation.as_ptr())
}

/// Deallocates memory that was allocated using `malloc_align`.
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
#[inline]
pub const fn align_offset(addr: usize, align: usize) -> usize {
    addr & (align - 1)
}

/// Checks whether the address has the demanded alignment.
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