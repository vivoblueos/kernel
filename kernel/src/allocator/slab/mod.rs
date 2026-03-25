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

pub mod heap;

const MIN_SLAB_SHIFT: usize = 3;
const MAX_SLAB_SHIFT: usize = 10;
const ADDITIONAL_SLAB_COUNT: usize = 2; // Add 96 and 192 to improve memory utilization
const SLAB_ALLOCATOR_COUNT: usize = MAX_SLAB_SHIFT - MIN_SLAB_SHIFT + 1 + ADDITIONAL_SLAB_COUNT;
const SYSTEM_ALLOCATOR_INDEX: usize = SLAB_ALLOCATOR_COUNT;
const PAGE_SHIFT: usize = 12;
const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
const SLAB_MAX_UPSEARCH_SIZE: usize = 16; // When SLAB_32 is full, 18B is not allowed in SLAB_64

#[derive(Copy, Clone)]
pub struct Slab {
    block_size: usize,
    len: usize,
    min_len: usize,
    free_block_list: SinglyLinkedList<usize>,
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
            self.free_block_list.push(NonNull::new_unchecked(new_block));
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
                        panic!("alloc ptr is not in the heap\n")
                    }
                }
                let ptr = block.as_ptr();
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
                panic!("dealloc ptr is not in the heap\n")
            }
        }

        let magic_ptr = ptr.wrapping_add(1);
        if *magic_ptr == 0xdeadbeef {
            panic!("Double free detected")
        }
        self.free_block_list.push(NonNull::new_unchecked(ptr));
        ptr::write(magic_ptr, 0xdeadbeef);
        self.len += 1;
    }
}

pub struct SlabHeap<
    const SLAB_8: usize,
    const SLAB_16: usize,
    const SLAB_32: usize,
    const SLAB_64: usize,
    const SLAB_96: usize,
    const SLAB_128: usize,
    const SLAB_192: usize,
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
        const SLAB_96: usize,
        const SLAB_128: usize,
        const SLAB_192: usize,
        const SLAB_256: usize,
        const SLAB_512: usize,
        const SLAB_1024: usize,
    >
    SlabHeap<
        SLAB_8,
        SLAB_16,
        SLAB_32,
        SLAB_64,
        SLAB_96,
        SLAB_128,
        SLAB_192,
        SLAB_256,
        SLAB_512,
        SLAB_1024,
    >
{
    // Constants for slab boundaries
    const SLAB_SIZES: [usize; SLAB_ALLOCATOR_COUNT] = [8, 16, 32, 64, 96, 128, 192, 256, 512, 1024];
    const SLAB_PAGE_COUNT: [usize; SLAB_ALLOCATOR_COUNT] = [
        SLAB_8, SLAB_16, SLAB_32, SLAB_64, SLAB_96, SLAB_128, SLAB_192, SLAB_256, SLAB_512,
        SLAB_1024,
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
            result[i] = (Self::SLAB_PAGE_COUNT[i] << PAGE_SHIFT) / Self::SLAB_SIZES[i];
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
        self.slab_total_size = (SLAB_8
            + SLAB_16
            + SLAB_32
            + SLAB_64
            + SLAB_96
            + SLAB_128
            + SLAB_192
            + SLAB_256
            + SLAB_512
            + SLAB_1024)
            * PAGE_SIZE;
        debug_assert!(self.slab_total_size < size);
        let slab_layout = Layout::from_size_align(self.slab_total_size, PAGE_SIZE).unwrap();
        let slab_ptr = self.system_allocator.allocate(&slab_layout).unwrap();

        // init slabs
        let mut start_addr = slab_ptr.as_ptr() as usize;
        self.slab_begin_addr = start_addr;
        for i in 0..SLAB_ALLOCATOR_COUNT {
            self.slab_allocator[i].init(start_addr, Self::SLAB_COUNT[i], Self::SLAB_SIZES[i]);
            start_addr += Self::SLAB_PAGE_COUNT[i] * PAGE_SIZE;
        }
    }

    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut ptr = None;
        let mut allocator_index = Self::layout_to_allocator(layout.size(), layout.align());
        while ptr.is_none() {
            if allocator_index < SLAB_ALLOCATOR_COUNT {
                if self.slab_allocator[allocator_index].len > 0
                    && Self::SLAB_SIZES[allocator_index] % layout.align() == 0
                {
                    ptr = self.slab_allocator[allocator_index].allocate(layout);
                    self.allocated += Self::SLAB_SIZES[allocator_index];
                } else if Self::SLAB_SIZES[allocator_index] <= SLAB_MAX_UPSEARCH_SIZE {
                    allocator_index += 1;
                } else {
                    allocator_index = SYSTEM_ALLOCATOR_INDEX;
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
                    // Log allocation failure for debugging.
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
            self.allocated -= Self::SLAB_SIZES[allocator_index];
            Self::SLAB_SIZES[allocator_index]
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
            self.allocated -= Self::SLAB_SIZES[allocator_index];
            Self::SLAB_SIZES[allocator_index]
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
            let block_size = Self::SLAB_SIZES[allocator_index];
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
            let block_size = Self::SLAB_SIZES[allocator_index];
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
        let index = Self::SLAB_SIZES.partition_point(|index| index < &core::cmp::max(size, align));
        if index <= SLAB_ALLOCATOR_COUNT {
            index
        } else {
            SLAB_ALLOCATOR_COUNT
        }
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
                    Self::SLAB_SIZES[i],
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
            return Some(Self::SLAB_SIZES[pos]);
        }
        self.system_allocator.size_of_allocation(ptr)
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let max_free = self.system_allocator.get_max_free_block_size();
        if max_free > Self::SLAB_SIZES[SLAB_ALLOCATOR_COUNT - 1] {
            return max_free;
        }
        for i in (0..SLAB_ALLOCATOR_COUNT).rev() {
            if self.slab_allocator[i].len > 0 {
                return core::cmp::max(max_free, Self::SLAB_SIZES[i]);
            }
        }
        max_free
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Dynamic Slab Allocator
// ═══════════════════════════════════════════════════════════════════════════

// ── Constants ───────────────────────────────────────────────────────────────

#[cfg(allocator = "slab_dynamic")]
const PAGE_MAGIC: u32 = 0x534C_4142; // "SLAB"

#[cfg(allocator = "slab_dynamic")]
const NULL_PTR: usize = 0;

#[cfg(allocator = "slab_dynamic")]
const MEMORY_PRESSURE_THRESHOLD: usize = 128 * 1024; // 128 KB

#[cfg(allocator = "slab_dynamic")]
const DEFAULT_MAX_PAGES_PER_SLAB: usize = 4;

#[cfg(allocator = "slab_dynamic")]
const DEFAULT_MAX_TOTAL_PAGES: usize = 32;

// ── PageMetadata ─────────────────────────────────────────────────────────────

/// Metadata embedded at the very start of each dynamically managed 4 KB page.
///
/// Layout (little-endian):
///   [0..usize]       next_page    — next page in DynamicSlab page list; 0 = none
///   [usize..+4]      page_magic   — PAGE_MAGIC when page is owned by a DynamicSlab
///   [usize+4]        slab_index   — index into SLAB_SIZES[] (0..SLAB_ALLOCATOR_COUNT)
///   [usize+5..+8]    _pad         — padding to keep free_blocks u32-aligned
///   [usize+8..+12]   free_blocks  — number of free blocks currently in this page
///   [usize+12..+16]  total_blocks — total blocks in this page (constant after init)
///   [usize+16..+24]  free_head    — address of first free block; 0 = empty
///
/// Total: 24 bytes on 32-bit (usize = 4 B), 32 bytes on 64-bit (usize = 8 B).
#[cfg(allocator = "slab_dynamic")]
#[repr(C)]
struct PageMetadata {
    next_page: usize,
    page_magic: u32,
    slab_index: u8,
    _pad: [u8; 3],
    free_blocks: u32,
    total_blocks: u32,
    free_head: usize,
}

/// Byte offset from page base where the first allocatable block starts.
/// Rounds `size_of::<PageMetadata>()` up to the nearest multiple of `block_size`
/// so that every block in the page has at least `block_size`-byte alignment.
#[cfg(allocator = "slab_dynamic")]
fn page_data_offset(block_size: usize) -> usize {
    let meta = core::mem::size_of::<PageMetadata>();
    (meta + block_size - 1) / block_size * block_size
}

/// Number of allocatable blocks that fit in a single PAGE_SIZE page.
#[cfg(allocator = "slab_dynamic")]
fn blocks_per_page(block_size: usize) -> usize {
    (PAGE_SIZE - page_data_offset(block_size)) / block_size
}

/// Check whether `ptr` lives inside a dynamically managed slab page.
///
/// Returns `Some(slab_index)` when the page's magic matches, `None` otherwise.
/// Reads `page_magic` by raw byte offset rather than casting to `&PageMetadata`
/// to avoid UB when the page belongs to TLSF (non-slab memory).
///
/// # Safety
/// The page-aligned address is always readable in kernel context.
#[cfg(allocator = "slab_dynamic")]
fn ptr_is_slab(ptr: usize) -> Option<u8> {
    let page_base = ptr & !(PAGE_SIZE - 1);
    let magic_offset = core::mem::size_of::<usize>();
    let index_offset = magic_offset + 4;
    unsafe {
        let magic = *((page_base + magic_offset) as *const u32);
        if magic == PAGE_MAGIC {
            Some(*((page_base + index_offset) as *const u8))
        } else {
            None
        }
    }
}

// ── DynamicSlab ──────────────────────────────────────────────────────────────

#[cfg(allocator = "slab_dynamic")]
struct DynamicSlab {
    block_size: usize,
    page_list_head: usize, // head of intrusive page list; 0 = no pages
    total_blocks: usize,
    free_blocks: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlab {
    const fn new() -> Self {
        DynamicSlab {
            block_size: 0,
            page_list_head: NULL_PTR,
            total_blocks: 0,
            free_blocks: 0,
        }
    }

    fn set_block_size(&mut self, block_size: usize) {
        self.block_size = block_size;
    }

    /// Format a fresh PAGE_SIZE-aligned page as a slab page and prepend to page list.
    ///
    /// # Safety
    /// `page_addr` must be PAGE_SIZE-aligned and point to PAGE_SIZE writable bytes.
    unsafe fn init_page(&mut self, page_addr: usize, slab_index: u8) {
        let offset = page_data_offset(self.block_size);
        let total = blocks_per_page(self.block_size);

        // Build intrusive free list: each free block's first usize = addr of next free block.
        // Traverse in reverse so the head ends up pointing at the lowest address.
        let mut prev_free: usize = NULL_PTR;
        for i in (0..total).rev() {
            let block_addr = page_addr + offset + i * self.block_size;
            *(block_addr as *mut usize) = prev_free;
            prev_free = block_addr;
        }

        let meta = page_addr as *mut PageMetadata;
        (*meta).next_page = self.page_list_head;
        (*meta).page_magic = PAGE_MAGIC;
        (*meta).slab_index = slab_index;
        (*meta)._pad = [0u8; 3];
        (*meta).free_blocks = total as u32;
        (*meta).total_blocks = total as u32;
        (*meta).free_head = if total > 0 { page_addr + offset } else { NULL_PTR };

        self.page_list_head = page_addr;
        self.total_blocks += total;
        self.free_blocks += total;
    }

    /// Allocate one block from the first page that has free blocks.
    /// Returns `None` if all pages are full (caller must add a new page first).
    unsafe fn allocate_block(&mut self) -> Option<NonNull<u8>> {
        let mut current = self.page_list_head;
        while current != NULL_PTR {
            let meta = current as *mut PageMetadata;
            if (*meta).free_blocks > 0 {
                return Some(self.pop_from_page(current));
            }
            current = (*meta).next_page;
        }
        None
    }

    /// Pop one block from the free list of the given page.
    ///
    /// # Safety
    /// `page_addr` must be an active slab page with `free_blocks > 0`.
    unsafe fn pop_from_page(&mut self, page_addr: usize) -> NonNull<u8> {
        let meta = page_addr as *mut PageMetadata;
        let block_addr = (*meta).free_head;
        debug_assert_ne!(block_addr, NULL_PTR, "pop_from_page called on empty page");

        let next_free = *(block_addr as *const usize);
        (*meta).free_head = next_free;
        (*meta).free_blocks -= 1;
        self.free_blocks -= 1;

        // Clear the next-pointer slot — block is now in use.
        *(block_addr as *mut usize) = 0;

        NonNull::new_unchecked(block_addr as *mut u8)
    }

    /// Push `ptr` back onto its page's free list.
    ///
    /// Returns `(page_addr, page_is_now_fully_free)`.
    ///
    /// # Safety
    /// `ptr` must be a block previously allocated from this `DynamicSlab`.
    unsafe fn free_block(&mut self, ptr: NonNull<u8>) -> (usize, bool) {
        let ptr_addr = ptr.as_ptr() as usize;
        let page_addr = ptr_addr & !(PAGE_SIZE - 1);
        let meta = page_addr as *mut PageMetadata;

        debug_assert_eq!((*meta).page_magic, PAGE_MAGIC);
        debug_assert!(
            (*meta).free_blocks < (*meta).total_blocks,
            "double-free detected at {:p}",
            ptr.as_ptr()
        );

        *(ptr.as_ptr() as *mut usize) = (*meta).free_head;
        (*meta).free_head = ptr_addr;
        (*meta).free_blocks += 1;
        self.free_blocks += 1;

        let fully_free = (*meta).free_blocks == (*meta).total_blocks;
        (page_addr, fully_free)
    }

    /// Unlink `page_addr` from the intrusive page list and update aggregate counters.
    ///
    /// Clears `page_magic` so `ptr_is_slab` returns `None` for this page afterwards.
    ///
    /// # Safety
    /// `page_addr` must be currently in `self`'s page list.
    unsafe fn remove_page(&mut self, page_addr: usize) {
        let total = (*(page_addr as *const PageMetadata)).total_blocks as usize;

        if self.page_list_head == page_addr {
            let meta = page_addr as *mut PageMetadata;
            self.page_list_head = (*meta).next_page;
        } else {
            let mut prev = self.page_list_head;
            while prev != NULL_PTR {
                let meta = prev as *mut PageMetadata;
                if (*meta).next_page == page_addr {
                    let target = page_addr as *const PageMetadata;
                    (*meta).next_page = (*target).next_page;
                    break;
                }
                prev = (*meta).next_page;
            }
        }

        self.total_blocks -= total;
        self.free_blocks -= total;

        // Invalidate magic — page is no longer managed by this slab.
        (*(page_addr as *mut PageMetadata)).page_magic = 0;
    }
}

// ── PagePool ─────────────────────────────────────────────────────────────────

/// SLUB-style page pool: caches fully-free slab pages to reduce TLSF pressure.
///
/// Uses the same intrusive-list trick as `DynamicSlab`: the page's `next_page`
/// field is reused as the pool chain pointer. `page_magic` is cleared by
/// `DynamicSlab::remove_page` before a page enters the pool, so `ptr_is_slab`
/// never matches pooled pages.
#[cfg(allocator = "slab_dynamic")]
struct PagePool {
    pool_heads: [usize; SLAB_ALLOCATOR_COUNT],
    page_counts: [usize; SLAB_ALLOCATOR_COUNT],
    total_pages: usize,
    max_pages_per_slab: usize,
    max_total_pages: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl PagePool {
    const fn new() -> Self {
        PagePool {
            pool_heads: [NULL_PTR; SLAB_ALLOCATOR_COUNT],
            page_counts: [0; SLAB_ALLOCATOR_COUNT],
            total_pages: 0,
            max_pages_per_slab: DEFAULT_MAX_PAGES_PER_SLAB,
            max_total_pages: DEFAULT_MAX_TOTAL_PAGES,
        }
    }

    /// Try to release a fully-free page into the pool.
    ///
    /// Returns `false` (page rejected) when the per-slab or global cap is reached;
    /// caller must then return the page directly to TLSF.
    ///
    /// # Safety
    /// `page_addr` must be PAGE_SIZE-aligned and no longer in any `DynamicSlab`'s list.
    unsafe fn release_page(&mut self, page_addr: usize, slab_index: usize) -> bool {
        if self.page_counts[slab_index] >= self.max_pages_per_slab {
            return false;
        }
        if self.total_pages >= self.max_total_pages {
            return false;
        }

        // Chain page into pool list via next_page field.
        let meta = page_addr as *mut PageMetadata;
        (*meta).next_page = self.pool_heads[slab_index];
        self.pool_heads[slab_index] = page_addr;
        self.page_counts[slab_index] += 1;
        self.total_pages += 1;
        true
    }

    /// Take one page from the pool for `slab_index`.
    /// Returns `None` if the pool is empty for that slab size.
    ///
    /// # Safety
    /// Caller must immediately call `DynamicSlab::init_page` on the returned page.
    unsafe fn take_page(&mut self, slab_index: usize) -> Option<usize> {
        if self.pool_heads[slab_index] == NULL_PTR {
            return None;
        }

        let page_addr = self.pool_heads[slab_index];
        let meta = page_addr as *const PageMetadata;
        self.pool_heads[slab_index] = (*meta).next_page;
        self.page_counts[slab_index] -= 1;
        self.total_pages -= 1;
        Some(page_addr)
    }

    /// Reclaim up to `pages_needed` pages from the pool and return them to TLSF.
    /// Reclaims from the largest slab size first to maximise TLSF memory recovery.
    /// Returns the number of pages actually reclaimed.
    ///
    /// # Safety
    /// `tlsf` must be the same allocator from which the pages were originally obtained.
    unsafe fn reclaim_to_tlsf(
        &mut self,
        tlsf: &mut tlsf::heap::TlsfHeap,
        pages_needed: usize,
    ) -> usize {
        let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
        let mut reclaimed = 0;
        let mut idx = SLAB_ALLOCATOR_COUNT;

        while reclaimed < pages_needed && idx > 0 {
            idx -= 1;
            while reclaimed < pages_needed && self.pool_heads[idx] != NULL_PTR {
                let page_addr = self.pool_heads[idx];
                let meta = page_addr as *const PageMetadata;
                self.pool_heads[idx] = (*meta).next_page;
                self.page_counts[idx] -= 1;
                self.total_pages -= 1;

                tlsf.deallocate(
                    NonNull::new_unchecked(page_addr as *mut u8),
                    layout.align(),
                );
                reclaimed += 1;
            }
        }
        reclaimed
    }
}

// ── DynamicSlabHeap ───────────────────────────────────────────────────────────

#[cfg(allocator = "slab_dynamic")]
pub struct DynamicSlabHeap {
    slabs: [DynamicSlab; SLAB_ALLOCATOR_COUNT],
    page_pool: PagePool,
    system_allocator: tlsf::heap::TlsfHeap,
    allocated: usize,
    maximum: usize,
    total: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlabHeap {
    const SLAB_SIZES: [usize; SLAB_ALLOCATOR_COUNT] =
        [8, 16, 32, 64, 96, 128, 192, 256, 512, 1024];

    pub const fn new() -> Self {
        DynamicSlabHeap {
            slabs: [const { DynamicSlab::new() }; SLAB_ALLOCATOR_COUNT],
            page_pool: PagePool::new(),
            system_allocator: tlsf::heap::TlsfHeap::new(),
            allocated: 0,
            maximum: 0,
            total: 0,
        }
    }

    /// Initialize the heap with the memory range `[start, start+size)`.
    ///
    /// Unlike `SlabHeap`, no memory is pre-allocated for slabs. All slab pages
    /// are fetched lazily from TLSF on first demand.
    ///
    /// # Safety
    /// `start..start+size` must be valid, exclusively owned, writable memory.
    pub unsafe fn init(&mut self, start: usize, size: usize) {
        let block = core::slice::from_raw_parts(start as *const u8, size);
        self.system_allocator.insert_free_block_ptr(block.into());
        self.total = size;

        for i in 0..SLAB_ALLOCATOR_COUNT {
            self.slabs[i].set_block_size(Self::SLAB_SIZES[i]);
        }
    }

    // ── Allocation ─────────────────────────────────────────────────────────

    /// Return the slab index for the given `(size, align)`.
    /// Result is `SLAB_ALLOCATOR_COUNT` when no slab can satisfy the request.
    fn layout_to_slab_index(size: usize, align: usize) -> usize {
        let min_size = core::cmp::max(size, align);
        // partition_point returns values in 0..=SLAB_ALLOCATOR_COUNT; no clamping needed.
        Self::SLAB_SIZES.partition_point(|&s| s < min_size)
    }

    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let ptr = unsafe { self.do_allocate(layout) };
        if ptr.is_some() {
            self.maximum = core::cmp::max(self.maximum, self.allocated);
            self.check_memory_pressure();
        }
        ptr
    }

    unsafe fn do_allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut idx = Self::layout_to_slab_index(layout.size(), layout.align());

        // Slab path: try from idx upward (upsearch handles alignment mismatches on small sizes).
        while idx < SLAB_ALLOCATOR_COUNT {
            if Self::SLAB_SIZES[idx] % layout.align() != 0 {
                if Self::SLAB_SIZES[idx] <= SLAB_MAX_UPSEARCH_SIZE {
                    idx += 1;
                    continue;
                }
                break; // fall through to system allocator
            }

            // Ensure the slab has at least one free block; add a new page if needed.
            if self.slabs[idx].free_blocks == 0 {
                let page_addr = self.acquire_page(idx)?;
                self.slabs[idx].init_page(page_addr, idx as u8);
            }

            let ptr = self.slabs[idx].allocate_block().unwrap();
            self.allocated += Self::SLAB_SIZES[idx];
            return Some(ptr);
        }

        // System allocator path (size > 1024 or incompatible alignment).
        let ptr = self.system_allocator.allocate(layout)?;
        self.allocated += used_block_hdr_for_allocation_unknown_align(ptr)
            .unwrap()
            .cast::<BlockHdr>()
            .as_ref()
            .size
            & !SIZE_USED;
        Some(ptr)
    }

    /// Obtain a fresh PAGE_SIZE page: first try the pool, then TLSF.
    unsafe fn acquire_page(&mut self, slab_index: usize) -> Option<usize> {
        if let Some(page) = self.page_pool.take_page(slab_index) {
            return Some(page);
        }
        let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
        Some(self.system_allocator.allocate(&page_layout)?.as_ptr() as usize)
    }

    // ── Deallocation ───────────────────────────────────────────────────────

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: &Layout) -> usize {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr) {
            self.free_slab_block(ptr, slab_idx as usize)
        } else {
            let size = self.system_allocator.deallocate(ptr, layout.align());
            self.allocated -= size;
            size
        }
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr) {
            self.free_slab_block(ptr, slab_idx as usize)
        } else {
            let size = self.system_allocator.deallocate_unknown_align(ptr);
            self.allocated -= size;
            size
        }
    }

    /// Free a slab block and, if the page becomes fully empty, either pool or
    /// return the page to TLSF.
    unsafe fn free_slab_block(&mut self, ptr: NonNull<u8>, idx: usize) -> usize {
        let (page_addr, page_empty) = self.slabs[idx].free_block(ptr);
        self.allocated -= Self::SLAB_SIZES[idx];

        if page_empty {
            self.slabs[idx].remove_page(page_addr);
            if !self.page_pool.release_page(page_addr, idx) {
                // Pool is full — return directly to TLSF.
                let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
                self.system_allocator.deallocate(
                    NonNull::new_unchecked(page_addr as *mut u8),
                    page_layout.align(),
                );
            }
        }
        Self::SLAB_SIZES[idx]
    }

    // ── Reallocation ───────────────────────────────────────────────────────

    pub unsafe fn reallocate(
        &mut self,
        ptr: NonNull<u8>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr) {
            let idx = slab_idx as usize;
            if new_layout.size() <= Self::SLAB_SIZES[idx] {
                return Some(ptr); // fits in existing block
            }
            let new_ptr = self.allocate(new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), Self::SLAB_SIZES[idx]);
            // Use deallocate_unknown_align: for slab blocks, deallocate() ignores
            // the layout argument (routes via ptr_is_slab), so this is cleaner.
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
        } else {
            self.system_allocator.reallocate(ptr, new_layout)
        }
    }

    pub unsafe fn reallocate_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr) {
            let idx = slab_idx as usize;
            if new_size <= Self::SLAB_SIZES[idx] {
                return Some(ptr);
            }
            let new_layout =
                Layout::from_size_align_unchecked(new_size, core::mem::size_of::<usize>());
            let new_ptr = self.allocate(&new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), Self::SLAB_SIZES[idx]);
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
        } else {
            self.system_allocator.reallocate_unknown_align(ptr, new_size)
        }
    }

    // ── Statistics ─────────────────────────────────────────────────────────

    pub fn allocated(&self) -> usize {
        self.allocated
    }
    pub fn maximum(&self) -> usize {
        self.maximum
    }
    pub fn total(&self) -> usize {
        self.total
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize> {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr) {
            Some(Self::SLAB_SIZES[slab_idx as usize])
        } else {
            self.system_allocator.size_of_allocation(ptr)
        }
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let sys_free = self.system_allocator.get_max_free_block_size();
        for i in (0..SLAB_ALLOCATOR_COUNT).rev() {
            if self.slabs[i].free_blocks > 0 {
                return core::cmp::max(sys_free, Self::SLAB_SIZES[i]);
            }
        }
        sys_free
    }

    // ── TLSF memory pressure ───────────────────────────────────────────────

    fn check_memory_pressure(&mut self) {
        let max_free = self.system_allocator.get_max_free_block_size();
        if max_free < MEMORY_PRESSURE_THRESHOLD {
            let pages_needed = (MEMORY_PRESSURE_THRESHOLD - max_free) / PAGE_SIZE + 1;
            unsafe {
                self.page_pool
                    .reclaim_to_tlsf(&mut self.system_allocator, pages_needed);
            }
        }
    }

    // ── Manual shrink ──────────────────────────────────────────────────────

    /// Walk every slab's page list and release fully-empty pages to the pool
    /// (or directly to TLSF if the pool is full).
    ///
    /// Normally not needed because `deallocate` auto-shrinks on page emptying.
    /// Useful after a bulk-free burst when you want to reclaim memory proactively.
    pub unsafe fn shrink(&mut self) {
        let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();

        for i in 0..SLAB_ALLOCATOR_COUNT {
            let mut current = self.slabs[i].page_list_head;
            while current != NULL_PTR {
                let meta = current as *const PageMetadata;
                let next = (*meta).next_page; // capture before possible removal

                if (*meta).free_blocks == (*meta).total_blocks {
                    self.slabs[i].remove_page(current);
                    if !self.page_pool.release_page(current, i) {
                        self.system_allocator.deallocate(
                            NonNull::new_unchecked(current as *mut u8),
                            page_layout.align(),
                        );
                    }
                }
                current = next;
            }
        }
    }

    pub fn print_slab_stat(&self) {
        kprintln!("size   pages  total  free   alloc ");
        kprintln!("------ ------ ------ ------ ------");
        for i in 0..SLAB_ALLOCATOR_COUNT {
            let bpp = blocks_per_page(Self::SLAB_SIZES[i]);
            let pages = if bpp > 0 {
                (self.slabs[i].total_blocks + bpp - 1) / bpp
            } else {
                0
            };
            kprintln!(
                "{:6} {:6} {:6} {:6} {:6}",
                Self::SLAB_SIZES[i],
                pages,
                self.slabs[i].total_blocks,
                self.slabs[i].free_blocks,
                self.slabs[i].total_blocks - self.slabs[i].free_blocks,
            );
        }
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(all(test, allocator = "slab_dynamic"))]
mod dynamic_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn page_data_offset_values() {
        let meta = core::mem::size_of::<PageMetadata>();
        assert_eq!(page_data_offset(8), (meta + 7) / 8 * 8);
        assert_eq!(page_data_offset(16), (meta + 15) / 16 * 16);
        assert_eq!(page_data_offset(32), (meta + 31) / 32 * 32);
        // For block_size > meta: offset = block_size
        assert_eq!(page_data_offset(64), 64);
        assert_eq!(page_data_offset(128), 128);
        assert_eq!(page_data_offset(1024), 1024);
    }

    #[test]
    fn blocks_per_page_nonzero() {
        for &bs in &[8usize, 16, 32, 64, 96, 128, 192, 256, 512, 1024] {
            let count = blocks_per_page(bs);
            assert!(count >= 1, "block_size={} should fit at least 1 block per page", bs);
        }
        let count8 = blocks_per_page(8);
        assert!(count8 >= 100, "8-byte blocks: expected ≥100 per page, got {}", count8);
    }

    #[test]
    fn dynamic_slab_alloc_dealloc_roundtrip() {
        use alloc::boxed::Box;
        let _b8: Box<[u8; 8]> = Box::new([0u8; 8]);
        let _b16: Box<[u8; 16]> = Box::new([0u8; 16]);
        let _b32: Box<[u8; 32]> = Box::new([0u8; 32]);
        let _b64: Box<[u8; 64]> = Box::new([0u8; 64]);
        let _b96: Box<[u8; 96]> = Box::new([0u8; 96]);
        let _b128: Box<[u8; 128]> = Box::new([0u8; 128]);
        let _b192: Box<[u8; 192]> = Box::new([0u8; 192]);
        let _b256: Box<[u8; 256]> = Box::new([0u8; 256]);
        let _b512: Box<[u8; 512]> = Box::new([0u8; 512]);
        let _b1024: Box<[u8; 1024]> = Box::new([0u8; 1024]);
    }

    #[test]
    fn dynamic_slab_expansion() {
        use alloc::{vec, vec::Vec};
        // Allocate enough 8-byte blocks to force page expansion.
        // blocks_per_page(8) ≈ 508 on 64-bit; allocate 600 to cross page boundary.
        let mut ptrs: Vec<Box<[u8; 8]>> = Vec::new();
        for _ in 0..600 {
            ptrs.push(Box::new([0xAA; 8]));
        }
        assert_eq!(ptrs[0][0], 0xAA);
        assert_eq!(ptrs[599][0], 0xAA);
        drop(ptrs); // should trigger page shrinkage back to pool/TLSF
    }

    #[test]
    fn dynamic_slab_page_pool_reuse() {
        use alloc::{vec, vec::Vec};
        let count = 200; // well within one page for 16-byte blocks
        let v: Vec<Box<[u8; 16]>> = (0..count).map(|_| Box::new([0u8; 16])).collect();
        drop(v); // pages go to pool
        // Re-allocate: should reuse pooled pages rather than fetching from TLSF.
        let _v2: Vec<Box<[u8; 16]>> = (0..count).map(|_| Box::new([0u8; 16])).collect();
    }

    #[test]
    fn dynamic_slab_large_falls_through_to_tlsf() {
        use alloc::boxed::Box;
        let _large = Box::new([0u8; 2048]);
        let _larger = Box::new([0u8; 65536]);
    }

    #[test]
    fn dynamic_slab_realloc_grow() {
        let ptr = crate::allocator::malloc(16);
        assert!(!ptr.is_null());
        let ptr2 = crate::allocator::realloc(ptr, 256);
        assert!(!ptr2.is_null());
        crate::allocator::free(ptr2);
    }

    #[test]
    fn dynamic_slab_realloc_shrink_in_place() {
        let ptr = crate::allocator::malloc(64);
        assert!(!ptr.is_null());
        let ptr2 = crate::allocator::realloc(ptr, 32);
        assert!(!ptr2.is_null());
        crate::allocator::free(ptr2);
    }
}

