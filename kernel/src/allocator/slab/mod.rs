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

use crate::allocator::{
    block::{used_block_hdr_for_allocation_unknown_align, BlockHdr, SIZE_USED},
    tlsf,
};
use blueos_infra::list::singly_linked_list::SinglyLinkedList;
use core::{alloc::Layout, mem, ptr, ptr::NonNull};
use log::{debug, warn};

pub mod heap;

const PAGE_SIZE: usize = 4096;
const PAGE_SHIFT: usize = 12;

pub struct Slab {
    block_size: usize,
    len: usize,
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
    }

    pub fn allocate(&mut self, _layout: &Layout) -> Option<NonNull<u8>> {
        match self.free_block_list.pop() {
            Some(block) => {
                self.len -= 1;
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

#[derive(Copy, Clone)]
pub enum HeapAllocator {
    Slab16Bytes = 0,
    Slab32Bytes,
    Slab64Bytes,
    Slab128Bytes,
    Slab256Bytes,
    Slab512Bytes,
    Slab1024Bytes,
    SystemAllocator,
}

impl HeapAllocator {
    pub fn block_size(&self) -> usize {
        match self {
            HeapAllocator::Slab16Bytes => 16,
            HeapAllocator::Slab32Bytes => 32,
            HeapAllocator::Slab64Bytes => 64,
            HeapAllocator::Slab128Bytes => 128,
            HeapAllocator::Slab256Bytes => 256,
            HeapAllocator::Slab512Bytes => 512,
            HeapAllocator::Slab1024Bytes => 1024,
            _ => unreachable!("not a block!"),
        }
    }
}

pub struct SlabHeap<
    const SLAB_16: usize,
    const SLAB_32: usize,
    const SLAB_64: usize,
    const SLAB_128: usize,
    const SLAB_256: usize,
    const SLAB_512: usize,
    const SLAB_1024: usize,
> {
    slab_16_bytes: Slab,
    slab_32_bytes: Slab,
    slab_64_bytes: Slab,
    slab_128_bytes: Slab,
    slab_256_bytes: Slab,
    slab_512_bytes: Slab,
    slab_1024_bytes: Slab,
    system_allocator: tlsf::heap::TlsfHeap,
    slab_begin_addr: usize,
    slab_total_size: usize,
    // statistics
    allocated: usize,
    maximum: usize,
    total: usize,
}

impl<
        const SLAB_16: usize,
        const SLAB_32: usize,
        const SLAB_64: usize,
        const SLAB_128: usize,
        const SLAB_256: usize,
        const SLAB_512: usize,
        const SLAB_1024: usize,
    > SlabHeap<SLAB_16, SLAB_32, SLAB_64, SLAB_128, SLAB_256, SLAB_512, SLAB_1024>
{
    // Constants for slab boundaries
    const SLAB_32_END: usize = SLAB_16 + SLAB_32;
    const SLAB_64_END: usize = Self::SLAB_32_END + SLAB_64;
    const SLAB_128_END: usize = Self::SLAB_64_END + SLAB_128;
    const SLAB_256_END: usize = Self::SLAB_128_END + SLAB_256;
    const SLAB_512_END: usize = Self::SLAB_256_END + SLAB_512;
    const SLAB_1024_END: usize = Self::SLAB_512_END + SLAB_1024;

    /// Create an empty heap
    pub const fn new() -> Self {
        Self {
            slab_16_bytes: Slab::new(),
            slab_32_bytes: Slab::new(),
            slab_64_bytes: Slab::new(),
            slab_128_bytes: Slab::new(),
            slab_256_bytes: Slab::new(),
            slab_512_bytes: Slab::new(),
            slab_1024_bytes: Slab::new(),
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
            (SLAB_16 + SLAB_32 + SLAB_64 + SLAB_128 + SLAB_256 + SLAB_512 + SLAB_1024) * PAGE_SIZE;
        assert!(self.slab_total_size < size);
        let slab_layout = Layout::from_size_align(self.slab_total_size, PAGE_SIZE).unwrap();
        let slab_ptr = self.system_allocator.allocate(&slab_layout).unwrap();

        // init slabs
        let mut start_addr = slab_ptr.as_ptr() as usize;
        self.slab_begin_addr = start_addr;
        self.slab_16_bytes.init(start_addr, SLAB_16 << (12 - 4), 16);
        start_addr += SLAB_16 * PAGE_SIZE;
        self.slab_32_bytes.init(start_addr, SLAB_32 << (12 - 5), 32);
        start_addr += SLAB_32 * PAGE_SIZE;
        self.slab_64_bytes.init(start_addr, SLAB_64 << (12 - 6), 64);
        start_addr += SLAB_64 * PAGE_SIZE;
        self.slab_128_bytes
            .init(start_addr, SLAB_128 << (12 - 7), 128);
        start_addr += SLAB_128 * PAGE_SIZE;
        self.slab_256_bytes
            .init(start_addr, SLAB_256 << (12 - 8), 256);
        start_addr += SLAB_256 * PAGE_SIZE;
        self.slab_512_bytes
            .init(start_addr, SLAB_512 << (12 - 9), 512);
        start_addr += SLAB_512 * PAGE_SIZE;
        self.slab_1024_bytes
            .init(start_addr, SLAB_1024 << (12 - 10), 1024);
    }

    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut ptr = None;
        let mut current_allocator = Self::layout_to_allocator(layout.size(), layout.align());
        while ptr.is_none() {
            match current_allocator {
                HeapAllocator::Slab16Bytes => {
                    if self.slab_16_bytes.len > 0 {
                        ptr = self.slab_16_bytes.allocate(layout);
                        self.allocated += 16;
                    } else {
                        current_allocator = HeapAllocator::Slab32Bytes;
                    }
                }
                HeapAllocator::Slab32Bytes => {
                    if self.slab_32_bytes.len > 0 {
                        ptr = self.slab_32_bytes.allocate(layout);
                        self.allocated += 32;
                    } else {
                        current_allocator = HeapAllocator::Slab64Bytes;
                    }
                }
                HeapAllocator::Slab64Bytes => {
                    if self.slab_64_bytes.len > 0 {
                        ptr = self.slab_64_bytes.allocate(layout);
                        self.allocated += 64;
                    } else {
                        current_allocator = HeapAllocator::Slab128Bytes;
                    }
                }
                HeapAllocator::Slab128Bytes => {
                    if self.slab_128_bytes.len > 0 {
                        ptr = self.slab_128_bytes.allocate(layout);
                        self.allocated += 128;
                    } else {
                        current_allocator = HeapAllocator::Slab256Bytes;
                    }
                }
                HeapAllocator::Slab256Bytes => {
                    if self.slab_256_bytes.len > 0 {
                        ptr = self.slab_256_bytes.allocate(layout);
                        self.allocated += 256;
                    } else {
                        current_allocator = HeapAllocator::Slab512Bytes;
                    }
                }
                HeapAllocator::Slab512Bytes => {
                    if self.slab_512_bytes.len > 0 {
                        ptr = self.slab_512_bytes.allocate(layout);
                        self.allocated += 512;
                    } else {
                        current_allocator = HeapAllocator::Slab1024Bytes;
                    }
                }
                HeapAllocator::Slab1024Bytes => {
                    if self.slab_1024_bytes.len > 0 {
                        ptr = self.slab_1024_bytes.allocate(layout);
                        self.allocated += 1024;
                    } else {
                        current_allocator = HeapAllocator::SystemAllocator;
                    }
                }
                HeapAllocator::SystemAllocator => {
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
        }

        // Update maximum usage
        if ptr.is_some() {
            self.maximum = core::cmp::max(self.maximum, self.allocated);
        }

        ptr
    }

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: &Layout) -> usize {
        let allocator = self.ptr_to_allocator(ptr.as_ptr() as usize);
        match allocator {
            HeapAllocator::SystemAllocator => {
                let size = self.system_allocator.deallocate(ptr, layout.align());
                self.allocated -= size;
                size
            }
            HeapAllocator::Slab16Bytes => {
                self.slab_16_bytes.deallocate(ptr);
                self.allocated -= 16;
                16
            }
            HeapAllocator::Slab32Bytes => {
                self.slab_32_bytes.deallocate(ptr);
                self.allocated -= 32;
                32
            }
            HeapAllocator::Slab64Bytes => {
                self.slab_64_bytes.deallocate(ptr);
                self.allocated -= 64;
                64
            }
            HeapAllocator::Slab128Bytes => {
                self.slab_128_bytes.deallocate(ptr);
                self.allocated -= 128;
                128
            }
            HeapAllocator::Slab256Bytes => {
                self.slab_256_bytes.deallocate(ptr);
                self.allocated -= 256;
                256
            }
            HeapAllocator::Slab512Bytes => {
                self.slab_512_bytes.deallocate(ptr);
                self.allocated -= 512;
                512
            }
            HeapAllocator::Slab1024Bytes => {
                self.slab_1024_bytes.deallocate(ptr);
                self.allocated -= 1024;
                1024
            }
        }
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let allocator = self.ptr_to_allocator(ptr.as_ptr() as usize);
        match allocator {
            HeapAllocator::SystemAllocator => {
                let size = self.system_allocator.deallocate_unknown_align(ptr);
                self.allocated -= size;
                size
            }
            HeapAllocator::Slab16Bytes => {
                self.slab_16_bytes.deallocate(ptr);
                self.allocated -= 16;
                16
            }
            HeapAllocator::Slab32Bytes => {
                self.slab_32_bytes.deallocate(ptr);
                self.allocated -= 32;
                32
            }
            HeapAllocator::Slab64Bytes => {
                self.slab_64_bytes.deallocate(ptr);
                self.allocated -= 64;
                64
            }
            HeapAllocator::Slab128Bytes => {
                self.slab_128_bytes.deallocate(ptr);
                self.allocated -= 128;
                128
            }
            HeapAllocator::Slab256Bytes => {
                self.slab_256_bytes.deallocate(ptr);
                self.allocated -= 256;
                256
            }
            HeapAllocator::Slab512Bytes => {
                self.slab_512_bytes.deallocate(ptr);
                self.allocated -= 512;
                512
            }
            HeapAllocator::Slab1024Bytes => {
                self.slab_1024_bytes.deallocate(ptr);
                self.allocated -= 1024;
                1024
            }
        }
    }

    pub unsafe fn reallocate(
        &mut self,
        ptr: NonNull<u8>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        let allocator = self.ptr_to_allocator(ptr.as_ptr() as usize);
        match allocator {
            HeapAllocator::SystemAllocator => self.system_allocator.reallocate(ptr, new_layout),
            block_allocator => {
                let block_size = block_allocator.block_size();
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
    }

    pub unsafe fn reallocate_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let allocator = self.ptr_to_allocator(ptr.as_ptr() as usize);
        match allocator {
            HeapAllocator::SystemAllocator => self
                .system_allocator
                .reallocate_unknown_align(ptr, new_size),
            block_allocator => {
                let block_size = block_allocator.block_size();
                if new_size <= block_size {
                    return Some(ptr);
                }
                let new_layout =
                    Layout::from_size_align_unchecked(new_size, mem::size_of::<usize>());
                let new_ptr = self.allocate(&new_layout)?;
                core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), block_size);
                let old_size = self.deallocate(ptr, &new_layout);
                self.allocated += new_size - old_size;
                Some(new_ptr)
            }
        }
    }

    // Finds the appropriate allocator based on layout size and alignment
    //
    // This function implements a best-fit strategy for slab allocation:
    // - For sizes > 256 bytes, use the system allocator
    // - For smaller sizes, use the smallest slab that can accommodate both size and alignment
    fn layout_to_allocator(size: usize, align: usize) -> HeapAllocator {
        if size > 1024 {
            HeapAllocator::SystemAllocator
        } else if size <= 16 && align <= 16 {
            HeapAllocator::Slab16Bytes
        } else if size <= 32 && align <= 32 {
            HeapAllocator::Slab32Bytes
        } else if size <= 64 && align <= 64 {
            HeapAllocator::Slab64Bytes
        } else if size <= 128 && align <= 128 {
            HeapAllocator::Slab128Bytes
        } else if size <= 256 && align <= 256 {
            HeapAllocator::Slab256Bytes
        } else if size <= 512 && align <= 512 {
            HeapAllocator::Slab512Bytes
        } else {
            HeapAllocator::Slab1024Bytes
        }
    }

    fn ptr_to_allocator(&mut self, ptr: usize) -> HeapAllocator {
        if ptr < self.slab_begin_addr {
            return HeapAllocator::SystemAllocator;
        }
        let offset = ptr - self.slab_begin_addr;
        let slab_index = offset >> PAGE_SHIFT;

        if slab_index < SLAB_16 {
            HeapAllocator::Slab16Bytes
        } else if slab_index < Self::SLAB_32_END {
            HeapAllocator::Slab32Bytes
        } else if slab_index < Self::SLAB_64_END {
            HeapAllocator::Slab64Bytes
        } else if slab_index < Self::SLAB_128_END {
            HeapAllocator::Slab128Bytes
        } else if slab_index < Self::SLAB_256_END {
            HeapAllocator::Slab256Bytes
        } else if slab_index < Self::SLAB_512_END {
            HeapAllocator::Slab512Bytes
        } else if slab_index < Self::SLAB_1024_END {
            HeapAllocator::Slab1024Bytes
        } else {
            HeapAllocator::SystemAllocator
        }
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

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize> {
        let raw_ptr = ptr.as_ptr() as usize;
        if raw_ptr < self.slab_begin_addr {
            return self.system_allocator.size_of_allocation(ptr);
        }
        let offset = raw_ptr - self.slab_begin_addr;
        let slab_index = offset >> 12;

        if slab_index < SLAB_16 {
            Some(16)
        } else if slab_index < Self::SLAB_32_END {
            Some(32)
        } else if slab_index < Self::SLAB_64_END {
            Some(64)
        } else if slab_index < Self::SLAB_128_END {
            Some(128)
        } else if slab_index < Self::SLAB_256_END {
            Some(256)
        } else if slab_index < Self::SLAB_512_END {
            Some(512)
        } else if slab_index < Self::SLAB_1024_END {
            Some(1024)
        } else {
            self.system_allocator.size_of_allocation(ptr)
        }
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let max_free = self.system_allocator.get_max_free_block_size();
        if max_free > 1024 {
            return max_free;
        }
        if self.slab_1024_bytes.len > 0 {
            return 1024;
        }
        if self.slab_512_bytes.len > 0 {
            return core::cmp::max(max_free, 512);
        }
        if self.slab_256_bytes.len > 0 {
            return core::cmp::max(max_free, 256);
        }
        if self.slab_128_bytes.len > 0 {
            return core::cmp::max(max_free, 128);
        }
        if self.slab_64_bytes.len > 0 {
            return core::cmp::max(max_free, 64);
        }
        if self.slab_32_bytes.len > 0 {
            return core::cmp::max(max_free, 32);
        }
        if self.slab_16_bytes.len > 0 {
            return core::cmp::max(max_free, 16);
        }
        max_free
    }
}
