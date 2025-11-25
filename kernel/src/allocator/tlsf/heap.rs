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

use super::Tlsf;
use crate::{allocator, sync::spinlock::SpinLock};
use const_default::ConstDefault;
use core::{alloc::Layout, ptr::NonNull};

use allocator::MemoryInfo;

pub type TlsfHeap = Tlsf<'static, usize, usize, { usize::BITS as usize }, { usize::BITS as usize }>;

/// A two-Level segregated fit heap.
pub struct Heap {
    heap: SpinLock<TlsfHeap>,
}

impl Heap {
    // Create a new UNINITIALIZED heap allocator
    pub const fn new() -> Self {
        Heap {
            heap: SpinLock::new(ConstDefault::DEFAULT),
        }
    }

    // Initializes the heap
    pub unsafe fn init(&self, start_addr: usize, size: usize) {
        let block: &[u8] = core::slice::from_raw_parts(start_addr as *const u8, size);
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(!heap.is_inited());
        heap.insert_free_block_ptr(block.into());
    }

    // try to allocate memory with the given layout
    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        heap.allocate(&layout)
    }

    // deallocate the memory pointed by ptr with the given layout
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_valid_ptr(ptr));
        heap.deallocate(NonNull::new_unchecked(ptr), layout.align());
    }

    pub unsafe fn deallocate_unknown_align(&self, ptr: *mut u8) {
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_valid_ptr(ptr));
        heap.deallocate_unknown_align(NonNull::new_unchecked(ptr));
    }

    // reallocate memory with the given size and layout
    pub unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        heap.reallocate(NonNull::new_unchecked(ptr), &new_layout)
    }

    // reallocate memory with the given size but with out align
    pub unsafe fn realloc_unknown_align(
        &self,
        ptr: *mut u8,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        heap.reallocate_unknown_align(NonNull::new_unchecked(ptr), new_size)
    }

    // Retrieves various statistics about the current state of the heap's memory usage.
    pub fn memory_info(&self) -> MemoryInfo {
        let heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_inited());
        MemoryInfo {
            total: heap.total(),
            used: heap.allocated(),
            max_used: heap.maximum(),
        }
    }

    // Get size of max free block in this Heap
    pub unsafe fn get_max_free_block_size(&self) -> usize {
        let heap = self.heap.irqsave_lock();
        heap.get_max_free_block_size()
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> usize {
        let mut heap = self.heap.irqsave_lock();
        #[cfg(debugging_allocator)]
        debug_assert!(heap.is_valid_ptr(ptr.as_ptr()));
        heap.size_of_allocation(ptr).unwrap_or(0)
    }
}
