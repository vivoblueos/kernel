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

use super::SlabHeap as Slab;
use crate::{allocator::MemoryInfo, sync::spinlock::SpinLock};
use core::{alloc::Layout, ptr::NonNull};

type SlabHeap = Slab<2, 4, 2, 1, 1, 1, 1, 1>;
pub struct Heap {
    heap: SpinLock<SlabHeap>,
}

impl Heap {
    // Create a new UNINITIALIZED heap allocator
    pub const fn new() -> Self {
        Heap {
            heap: SpinLock::new(SlabHeap::new()),
        }
    }

    // Initializes the heap
    // Safety: the memory start address and size must be valid.
    pub unsafe fn init(&self, start_addr: usize, size: usize) {
        let mut heap = self.heap.irqsave_lock();
        heap.init(start_addr, size);
    }

    // try to allocate memory with the given layout
    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.allocate(&layout)
    }

    // deallocate the memory pointed by ptr with the given layout
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate(NonNull::new_unchecked(ptr), &layout);
    }

    // deallocate the memory pointed by ptr with out align
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn deallocate_unknown_align(&self, ptr: *mut u8) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate_unknown_align(NonNull::new_unchecked(ptr));
    }

    // reallocate memory with the given size and layout
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate(NonNull::new_unchecked(ptr), &new_layout)
    }

    // reallocate memory with the given size but with out align
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn realloc_unknown_align(
        &self,
        ptr: *mut u8,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate_unknown_align(NonNull::new_unchecked(ptr), new_size)
    }

    // Retrieves various statistics about the current state of the heap's memory usage.
    pub fn memory_info(&self) -> MemoryInfo {
        let heap = self.heap.irqsave_lock();
        MemoryInfo {
            total: heap.total(),
            used: heap.allocated(),
            max_used: heap.maximum(),
        }
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> usize {
        let mut heap = self.heap.irqsave_lock();
        heap.size_of_allocation(ptr).unwrap_or(0)
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let heap = self.heap.irqsave_lock();
        heap.get_max_free_block_size()
    }
}
