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

// This code is based on https://github.com/weclaw1/slab_allocator/blob/master/src/slab.rs
// Copyright (c) 2017 Robert Węcławski
// SPDX-LICENSE: MIT

use crate::{
    allocator::{
        block::{used_block_hdr_for_allocation_unknown_align, BlockHdr, SIZE_USED},
        tlsf,
    },
    kprintln,
};
use blueos_infra::list::singly_linked_list::SinglyLinkedList;
use core::{alloc::Layout, mem, ptr, ptr::NonNull};
use log::{debug, warn};

pub mod heap;

const MIN_SLAB_SHIFT: usize = 3;
const MAX_SLAB_SHIFT: usize = 10;
const SLAB_ALLOCATOR_COUNT: usize = MAX_SLAB_SHIFT - MIN_SLAB_SHIFT + 1;
const SYSTEM_ALLOCATOR_INDEX: usize = SLAB_ALLOCATOR_COUNT;
const PAGE_SHIFT: usize = 12;
const PAGE_SIZE: usize = 1 << PAGE_SHIFT;

#[derive(Copy, Clone)]
pub struct Slab {
    block_size: usize,
    len: usize,
    min_len: usize,
    free_block_list: SinglyLinkedList,
    #[cfg(debug_slab)]
    start_addr: usize,
    #[cfg(debug_slab)]
    end_addr: usize,
}

impl Slab {
    /// Create an empty heap
    pub const fn new() -> Self {
        Slab {
            block_size: 0,
            len: 0,
            min_len: 0,
            free_block_list: SinglyLinkedList::new(),
            #[cfg(debug_slab)]
            start_addr: 0,
            #[cfg(debug_slab)]
            end_addr: 0,
        }
    }

    pub unsafe fn init(&mut self, start_addr: usize, count: usize, block_size: usize) {
        self.block_size = block_size;
        #[cfg(debug_slab)]
        {
            self.start_addr = start_addr;
            self.end_addr = start_addr + count * block_size;
        }
        for i in (0..count).rev() {
            let new_block = (start_addr + i * block_size) as *mut usize;
            self.free_block_list.push(new_block);
        }

        self.len = count;
        self.min_len = count;
    }

    pub fn allocate(&mut self, _layout: &Layout) -> Option<NonNull<u8>> {
        match self.free_block_list.pop() {
            Some(block) => {
                self.len -= 1;
                self.min_len = core::cmp::min(self.min_len, self.len);
                #[cfg(debug_slab)]
                {
                    if (block as usize) < self.start_addr || (block as usize) >= self.end_addr {
                        log::error!("ptr = 0x{:p} is not in the heap", block);
                        log::error!("size = {}", self.block_size);
                        panic!("alloc ptr is not in the heap\n");
                    }
                }
                let ptr = block as *mut usize;
                // clear the magic number
                let magic_ptr = ptr.wrapping_add(1);
                // Safety: magic_ptr is not null.
                unsafe { *magic_ptr = 0 };
                // Safety: ptr is not null.
                Some(unsafe { NonNull::new_unchecked(ptr as *mut u8) })
            }
            None => None, //Err(AllocErr)
        }
    }

    /// Safety: ptr must have been previously allocated by self.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>) {
        // Since ptr was allocated by self, its alignment must be at least
        // the alignment of FreeBlock. Casting a less aligned pointer to
        // &mut FreeBlock would be undefined behavior.
        #[cfg_attr(feature = "clippy", allow(clippy::cast_ptr_alignment))]
        let ptr = ptr.as_ptr() as *mut usize;
        #[cfg(debug_slab)]
        {
            if (ptr as usize) < self.start_addr || (ptr as usize) >= self.end_addr {
                log::error!("ptr = 0x{:p} is not in the heap", ptr);
                log::error!("size = {}", self.block_size);
                panic!("dealloc ptr is not in the heap\n");
            }
        }

        let magic_ptr = ptr.wrapping_add(1);
        if *magic_ptr == 0xdeadbeef {
            log::warn!("0x{:p} is already freed", ptr);
            return;
        }
        self.free_block_list.push(ptr);
        ptr::write(magic_ptr, 0xdeadbeef);
        self.len += 1;
    }
}

pub struct SlabHeap<
    const SLAB_8: usize,
    const SLAB_16: usize,
    const SLAB_32: usize,
    const SLAB_64: usize,
    const SLAB_128: usize,
    const SLAB_256: usize,
    const SLAB_512: usize,
    const SLAB_1024: usize,
> {
    slab_allocator: [Slab; SLAB_ALLOCATOR_COUNT],
    system_allocator: tlsf::heap::TlsfHeap,
    slab_begin_addr: usize,
    slab_total_size: usize,
    // statistics
    allocated: usize,
    maximum: usize,
    total: usize,
}

impl<
        const SLAB_8: usize,
        const SLAB_16: usize,
        const SLAB_32: usize,
        const SLAB_64: usize,
        const SLAB_128: usize,
        const SLAB_256: usize,
        const SLAB_512: usize,
        const SLAB_1024: usize,
    > SlabHeap<SLAB_8, SLAB_16, SLAB_32, SLAB_64, SLAB_128, SLAB_256, SLAB_512, SLAB_1024>
{
    // Constants for slab boundaries
    const SLAB_PAGE_COUNT: [usize; SLAB_ALLOCATOR_COUNT] = [
        SLAB_8, SLAB_16, SLAB_32, SLAB_64, SLAB_128, SLAB_256, SLAB_512, SLAB_1024,
    ];
    const SLAB_PAGE_END: [usize; SLAB_ALLOCATOR_COUNT] = Self::get_slab_page_end();
    const SLAB_COUNT: [usize; SLAB_ALLOCATOR_COUNT] = Self::get_slab_count();

    const fn get_slab_page_end() -> [usize; SLAB_ALLOCATOR_COUNT] {
        let mut result = [0; SLAB_ALLOCATOR_COUNT];
        result[0] = Self::SLAB_PAGE_COUNT[0];
        let mut i = 1;
        while i < SLAB_ALLOCATOR_COUNT {
            result[i] = result[i - 1] + Self::SLAB_PAGE_COUNT[i];
            i += 1;
        }
        result
    }

    const fn get_slab_count() -> [usize; SLAB_ALLOCATOR_COUNT] {
        let mut result = [0; SLAB_ALLOCATOR_COUNT];
        let mut i = 0;
        while i < SLAB_ALLOCATOR_COUNT {
            result[i] = Self::SLAB_PAGE_COUNT[i] << (PAGE_SHIFT - (i + MIN_SLAB_SHIFT));
            i += 1;
        }
        result
    }

    /// Create an empty heap
    pub const fn new() -> Self {
        Self {
            slab_allocator: [const { Slab::new() }; SLAB_ALLOCATOR_COUNT],
            system_allocator: tlsf::heap::TlsfHeap::new(),
            slab_begin_addr: 0,
            slab_total_size: 0,
            allocated: 0,
            maximum: 0,
            total: 0,
        }
    }

    /// Add a range of memory [start, start+size) to the heap
    pub unsafe fn init(&mut self, start: usize, size: usize) {
        let block: &[u8] = core::slice::from_raw_parts(start as *const u8, size);
        self.system_allocator.insert_free_block_ptr(block.into());
        self.total = size;

        // allocate slabs
        self.slab_total_size =
            (SLAB_8 + SLAB_16 + SLAB_32 + SLAB_64 + SLAB_128 + SLAB_256 + SLAB_512 + SLAB_1024)
                * PAGE_SIZE;
        debug_assert!(self.slab_total_size < size);
        let slab_layout = Layout::from_size_align(self.slab_total_size, PAGE_SIZE).unwrap();
        let slab_ptr = self.system_allocator.allocate(&slab_layout).unwrap();

        // init slabs
        let mut start_addr = slab_ptr.as_ptr() as usize;
        self.slab_begin_addr = start_addr;
        for i in 0..SLAB_ALLOCATOR_COUNT {
            self.slab_allocator[i].init(start_addr, Self::SLAB_COUNT[i], 1 << (i + MIN_SLAB_SHIFT));
            start_addr += Self::SLAB_PAGE_COUNT[i] * PAGE_SIZE;
        }
    }

    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut ptr = None;
        let mut allocator_index = Self::layout_to_allocator(layout.size(), layout.align());
        while ptr.is_none() {
            if allocator_index < SLAB_ALLOCATOR_COUNT {
                if self.slab_allocator[allocator_index].len > 0 {
                    ptr = self.slab_allocator[allocator_index].allocate(layout);
                    self.allocated += 1 << (allocator_index + MIN_SLAB_SHIFT);
                } else {
                    allocator_index += 1;
                }
            } else {
                ptr = self.system_allocator.allocate(layout);
                if ptr.is_some() {
                    // Update allocated size for system allocator
                    self.allocated += unsafe {
                        used_block_hdr_for_allocation_unknown_align(ptr.unwrap())
                            .unwrap()
                            .cast::<BlockHdr>()
                            .as_ref()
                            .size
                            & !SIZE_USED
                    };
                } else {
                    // Log allocation failure for debugging
                    warn!(
                        "Allocation failed - size: {}, align: {}, total: {}, used: {}",
                        layout.size(),
                        layout.align(),
                        self.total,
                        self.allocated()
                    );
                    break;
                }
            }
        }

        // Update maximum usage
        if ptr.is_some() {
            self.maximum = core::cmp::max(self.maximum, self.allocated);
        }

        ptr
    }

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: &Layout) -> usize {
        let allocator_index = self.ptr_to_allocator(ptr.as_ptr() as usize);
        if allocator_index >= SLAB_ALLOCATOR_COUNT {
            let size = self.system_allocator.deallocate(ptr, layout.align());
            self.allocated -= size;
            size
        } else {
            self.slab_allocator[allocator_index].deallocate(ptr);
            self.allocated -= 1 << (allocator_index + MIN_SLAB_SHIFT);
            1 << (allocator_index + MIN_SLAB_SHIFT)
        }
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let allocator_index = self.ptr_to_allocator(ptr.as_ptr() as usize);
        if allocator_index >= SLAB_ALLOCATOR_COUNT {
            let size = self.system_allocator.deallocate_unknown_align(ptr);
            self.allocated -= size;
            size
        } else {
            self.slab_allocator[allocator_index].deallocate(ptr);
            self.allocated -= 1 << (allocator_index + MIN_SLAB_SHIFT);
            1 << (allocator_index + MIN_SLAB_SHIFT)
        }
    }

    pub unsafe fn reallocate(
        &mut self,
        ptr: NonNull<u8>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        let allocator_index = self.ptr_to_allocator(ptr.as_ptr() as usize);
        if allocator_index >= SLAB_ALLOCATOR_COUNT {
            self.system_allocator.reallocate(ptr, new_layout)
        } else {
            let block_size = 1 << (allocator_index + MIN_SLAB_SHIFT);
            if new_layout.size() <= block_size {
                return Some(ptr);
            }
            let new_ptr = self.allocate(new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), block_size);
            let old_size = self.deallocate(ptr, new_layout);
            self.allocated += new_layout.size() - old_size;
            Some(new_ptr)
        }
    }

    pub unsafe fn reallocate_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let allocator_index = self.ptr_to_allocator(ptr.as_ptr() as usize);
        if allocator_index >= SLAB_ALLOCATOR_COUNT {
            self.system_allocator
                .reallocate_unknown_align(ptr, new_size)
        } else {
            let block_size = 1 << (allocator_index + MIN_SLAB_SHIFT);
            if new_size <= block_size {
                return Some(ptr);
            }
            let new_layout = Layout::from_size_align_unchecked(new_size, mem::size_of::<usize>());
            let new_ptr = self.allocate(&new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), block_size);
            let old_size = self.deallocate(ptr, &new_layout);
            self.allocated += new_size - old_size;
            Some(new_ptr)
        }
    }

    // Finds the appropriate allocator based on layout size and alignment
    //
    // This function implements a best-fit strategy for slab allocation:
    // - For sizes > 1024 bytes, use the system allocator
    // - For smaller sizes, use the smallest slab that can accommodate both size and alignment
    fn layout_to_allocator(size: usize, align: usize) -> usize {
        let size_log2_ceil = core::cmp::max(Self::log2_ceil(size), Self::log2_ceil(align));
        if size_log2_ceil <= MAX_SLAB_SHIFT {
            size_log2_ceil.saturating_sub(MIN_SLAB_SHIFT)
        } else {
            MAX_SLAB_SHIFT
        }
    }

    #[inline]
    fn log2_ceil(n: usize) -> usize {
        if n <= 1 {
            return 0;
        }
        (usize::BITS - (n - 1).leading_zeros()) as usize
    }

    fn ptr_to_allocator(&mut self, ptr: usize) -> usize {
        if ptr < self.slab_begin_addr {
            return SYSTEM_ALLOCATOR_INDEX;
        }
        let offset = ptr - self.slab_begin_addr;
        let slab_index = offset >> PAGE_SHIFT;

        // Return SYSTEM_ALLOCATOR_INDEX if slab_index is not in SLAB_PAGE_END range
        Self::SLAB_PAGE_END.partition_point(|pos| pos <= &slab_index)
    }

    // Return the number of bytes that maximum used
    pub fn maximum(&self) -> usize {
        self.maximum
    }

    // Return the number of bytes that are actually allocated
    pub fn allocated(&self) -> usize {
        self.allocated
    }

    // Return the total number of bytes in the heap
    pub fn total(&self) -> usize {
        self.total
    }

    pub fn print_slab_stat(&self) {
        kprintln!("size   total  free   max    alloc ");
        kprintln!("------ ------ ------ ------ ------");
        for i in 0..SLAB_ALLOCATOR_COUNT {
            if Self::SLAB_PAGE_COUNT[i] != 0 {
                kprintln!(
                    "{:6} {:6} {:6} {:6} {:6}",
                    1 << (i + MIN_SLAB_SHIFT),
                    Self::SLAB_COUNT[i],
                    self.slab_allocator[i].len,
                    Self::SLAB_COUNT[i] - self.slab_allocator[i].min_len,
                    Self::SLAB_COUNT[i] - self.slab_allocator[i].len
                );
            }
        }
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize> {
        let raw_ptr = ptr.as_ptr() as usize;
        if raw_ptr < self.slab_begin_addr {
            return self.system_allocator.size_of_allocation(ptr);
        }
        let offset = raw_ptr - self.slab_begin_addr;
        let slab_index = offset >> PAGE_SHIFT;

        let pos = Self::SLAB_PAGE_END.partition_point(|pos| pos <= &slab_index);
        if pos < SLAB_ALLOCATOR_COUNT {
            return Some(1 << (pos + MIN_SLAB_SHIFT));
        }
        self.system_allocator.size_of_allocation(ptr)
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let max_free = self.system_allocator.get_max_free_block_size();
        if max_free > (1 << MAX_SLAB_SHIFT) {
            return max_free;
        }
        for i in (MIN_SLAB_SHIFT..=MAX_SLAB_SHIFT).rev() {
            if self.slab_allocator[i - MIN_SLAB_SHIFT].len > 0 {
                return core::cmp::max(max_free, 1 << i);
            }
        }
        max_free
    }
}
