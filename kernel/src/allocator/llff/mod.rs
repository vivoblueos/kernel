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

// This code is based on https://github.com/rust-osdev/linked-list-allocator/blob/main/src/lib.rs.
// Copyright (c) 2016 Philipp Oppermann
// SPDX-LICENSE: MIT

#![allow(dead_code)]
use core::{alloc::Layout, cmp, mem, ptr::NonNull};

use crate::{
    allocator::{
        block::{size_of_allocation, size_of_allocation_unknown_align},
        MemoryInfo,
    },
    sync::SpinLock,
};

pub mod heap;
mod hole;
use hole::HoleList;

/// A fixed size heap backed by a linked list of free memory blocks.
struct Heap {
    holes: HoleList,
    allocated: usize,
    maximum: usize,
}

unsafe impl Send for Heap {}

impl Heap {
    /// Creates an empty heap. All allocate calls will return `None`.
    pub const fn empty() -> Self {
        Self {
            allocated: 0,
            maximum: 0,
            holes: HoleList::empty(),
        }
    }

    /// Initializes an empty heap
    ///
    /// The `heap_bottom` pointer is automatically aligned, so the [`bottom()`][Self::bottom]
    /// method might return a pointer that is larger than `heap_bottom` after construction.
    ///
    /// The given `heap_size` must be large enough to store the required
    /// metadata, otherwise this function will panic. Depending on the
    /// alignment of the `hole_addr` pointer, the minimum size is between
    /// `2 * size_of::<usize>` and `3 * size_of::<usize>`.
    ///
    /// The usable size for allocations will be truncated to the nearest
    /// alignment of `align_of::<usize>`. Any extra bytes left at the end
    /// will be reclaimed once sufficient additional space is given to
    /// [`extend`][Heap::extend].
    ///
    /// # Safety
    ///
    /// This function must be called at most once and must only be used on an
    /// empty heap.
    ///
    /// The bottom address must be valid and the memory in the
    /// `[heap_bottom, heap_bottom + heap_size)` range must not be used for anything else.
    /// This function is unsafe because it can cause undefined behavior if the given address
    /// is invalid.
    ///
    /// The provided memory range must be valid for the `'static` lifetime.
    pub unsafe fn init(&mut self, heap_bottom: usize, heap_size: usize) {
        self.allocated = 0;
        self.maximum = 0;
        self.holes = HoleList::new(heap_bottom as *mut u8, heap_size);
    }

    /// Initialize an empty heap with provided memory.
    ///
    /// The caller is responsible for procuring a region of raw memory that may be utilized by the
    /// allocator. This might be done via any method such as (unsafely) taking a region from the
    /// program's memory, from a mutable static, or by allocating and leaking such memory from
    /// another allocator.
    ///
    /// The latter approach may be especially useful if the underlying allocator does not perform
    /// deallocation (e.g. a simple bump allocator). Then the overlaid linked-list-allocator can
    /// provide memory reclamation.
    ///
    /// The usable size for allocations will be truncated to the nearest
    /// alignment of `align_of::<usize>`. Any extra bytes left at the end
    /// will be reclaimed once sufficient additional space is given to
    /// [`extend`][Heap::extend].
    ///
    /// # Panics
    ///
    /// This method panics if the heap is already initialized.
    ///
    /// It also panics when the length of the given `mem` slice is not large enough to
    /// store the required metadata. Depending on the alignment of the slice, the minimum
    /// size is between `2 * size_of::<usize>` and `3 * size_of::<usize>`.
    pub fn init_from_slice(&mut self, mem: &'static mut [mem::MaybeUninit<u8>]) {
        assert!(
            self.bottom().is_null(),
            "The heap has already been initialized."
        );
        let size = mem.len();
        let address = mem.as_mut_ptr();
        // SAFETY: All initialization requires the bottom address to be valid, which implies it
        // must not be 0. Initially the address is 0. The assertion above ensures that no
        // initialization had been called before.
        // The given address and size is valid according to the safety invariants of the mutable
        // reference handed to us by the caller.
        unsafe { self.init(address as *mut u8 as usize, size) }
    }

    /// Creates a new heap with the given `bottom` and `size`.
    ///
    /// The `heap_bottom` pointer is automatically aligned, so the [`bottom()`][Self::bottom]
    /// method might return a pointer that is larger than `heap_bottom` after construction.
    ///
    /// The given `heap_size` must be large enough to store the required
    /// metadata, otherwise this function will panic. Depending on the
    /// alignment of the `hole_addr` pointer, the minimum size is between
    /// `2 * size_of::<usize>` and `3 * size_of::<usize>`.
    ///
    /// The usable size for allocations will be truncated to the nearest
    /// alignment of `align_of::<usize>`. Any extra bytes left at the end
    /// will be reclaimed once sufficient additional space is given to
    /// [`extend`][Heap::extend].
    ///
    /// # Safety
    ///
    /// The bottom address must be valid and the memory in the
    /// `[heap_bottom, heap_bottom + heap_size)` range must not be used for anything else.
    /// This function is unsafe because it can cause undefined behavior if the given address
    /// is invalid.
    ///
    /// The provided memory range must be valid for the `'static` lifetime.
    pub unsafe fn new(heap_bottom: *mut u8, heap_size: usize) -> Self {
        Self {
            allocated: 0,
            maximum: 0,
            holes: HoleList::new(heap_bottom, heap_size),
        }
    }

    /// Creates a new heap from a slice of raw memory.
    ///
    /// This is a convenience function that has the same effect as calling
    /// [`init_from_slice`] on an empty heap. All the requirements of `init_from_slice`
    /// apply to this function as well.
    pub fn from_slice(mem: &'static mut [mem::MaybeUninit<u8>]) -> Self {
        let size = mem.len();
        let address = mem.as_mut_ptr().cast();
        // SAFETY: The given address and size is valid according to the safety invariants of the
        // mutable reference handed to us by the caller.
        unsafe { Self::new(address, size) }
    }

    /// Allocates a chunk of the given size with the given alignment. Returns a pointer to the
    /// beginning of that chunk if it was successful. Else it returns `None`.
    /// This function scans the list of free memory blocks and uses the first block that is big
    /// enough. The runtime is in O(n) where n is the number of free blocks, but it should be
    /// reasonably fast for small allocations.
    //
    // NOTE: We could probably replace this with an `Option` instead of a `Result` in a later
    // release to remove this clippy warning
    #[allow(clippy::result_unit_err)]
    pub fn allocate_first_fit(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        match self.holes.allocate_first_fit(layout) {
            Ok((ptr, alloc_size)) => {
                self.allocated += alloc_size;
                self.maximum = cmp::max(self.maximum, self.allocated);
                Some(ptr)
            }
            Err(_err) => None,
        }
    }

    /// Frees the given allocation. `ptr` must be a pointer returned
    /// by a call to the `allocate_first_fit` function with identical size and alignment.
    ///
    /// This function walks the list of free memory blocks and inserts the freed block at the
    /// correct place. If the freed block is adjacent to another free block, the blocks are merged
    /// again. This operation is in `O(n)` since the list needs to be sorted by address.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer returned by a call to the [`allocate_first_fit`] function with
    /// identical layout. Undefined behavior may occur for invalid arguments.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: &Layout) -> usize {
        let free_size = self.holes.deallocate(ptr, &layout);
        self.allocated -= free_size;
        free_size
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let free_size = self.holes.deallocate_unknown_align(ptr);
        self.allocated -= free_size;
        free_size
    }

    pub unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: &Layout,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let old_size = size_of_allocation(ptr, layout.align())?;

        if new_size <= old_size {
            return Some(ptr);
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        // Allocate a whole new memory block
        let new_ptr = self.allocate_first_fit(&new_layout)?;
        // Move the existing data into the new location
        core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);
        // Deallocate the old memory block.
        self.deallocate(ptr, layout);
        self.allocated += new_size - old_size;

        Some(new_ptr)
    }

    pub unsafe fn realloc_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let old_size = size_of_allocation_unknown_align(ptr)?;
        if new_size <= old_size {
            return Some(ptr);
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, mem::size_of::<usize>());
        // Allocate a whole new memory block
        let new_ptr = self.allocate_first_fit(&new_layout)?;
        // Move the existing data into the new location
        core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);

        // Deallocate the old memory block.
        let old_size = self.deallocate_unknown_align(ptr);
        self.allocated += new_size - old_size;

        Some(new_ptr)
    }
    /// Returns the bottom address of the heap.
    ///
    /// The bottom pointer is automatically aligned, so the returned pointer
    /// might be larger than the bottom pointer used for initialization.
    pub fn bottom(&self) -> *mut u8 {
        self.holes.bottom
    }

    /// Returns the size of the heap.
    ///
    /// This is the size the heap is using for allocations, not necessarily the
    /// total amount of bytes given to the heap. To determine the exact memory
    /// boundaries, use [`bottom`][Self::bottom] and [`top`][Self::top].
    pub fn total(&self) -> usize {
        unsafe { self.holes.top.offset_from(self.holes.bottom) as usize }
    }

    /// Return the top address of the heap.
    ///
    /// Note: The heap may choose to not use bytes at the end for allocations
    /// until there is enough room for metadata, but it still retains ownership
    /// over memory from [`bottom`][Self::bottom] to the address returned.
    pub fn top(&self) -> *mut u8 {
        unsafe { self.holes.top.add(self.holes.pending_extend as usize) }
    }

    /// Returns the size of the maximum used of the heap
    pub fn maximum(&self) -> usize {
        self.maximum
    }

    /// Returns the size of the used part of the heap
    pub fn allocated(&self) -> usize {
        self.allocated
    }

    /// Returns the size of the free part of the heap
    pub fn free(&self) -> usize {
        self.total() - self.allocated
    }

    /// Extends the size of the heap by creating a new hole at the end.
    ///
    /// Small extensions are not guaranteed to grow the usable size of
    /// the heap. In order to grow the Heap most effectively, extend by
    /// at least `2 * size_of::<usize>`, keeping the amount a multiple of
    /// `size_of::<usize>`.
    ///
    /// Calling this method on an uninitialized Heap will panic.
    ///
    /// # Safety
    ///
    /// The amount of data given in `by` MUST exist directly after the original
    /// range of data provided when constructing the [Heap]. The additional data
    /// must have the same lifetime of the original range of data.
    ///
    /// Even if this operation doesn't increase the [usable size][`Self::size`]
    /// by exactly `by` bytes, those bytes are still owned by the Heap for
    /// later use.
    pub unsafe fn extend(&mut self, by: usize) {
        self.holes.extend(by);
    }
}
