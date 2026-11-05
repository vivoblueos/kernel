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
    block::{used_block_hdr_for_allocation_unknown_align, BlockHdr, SIZE_USED},
    tlsf,
};
use blueos_infra::{
    impl_simple_intrusive_adapter,
    list::{
        singly_linked_list::SinglyLinkedList,
        typed_ilist::{List, ListHead},
    },
};
use core::{alloc::Layout, mem, ptr, ptr::NonNull};

// `heap` module (SpinLock wrappers) is kept in kernel/kernel/src/allocator/slab/heap.rs

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
        }
    }

    pub unsafe fn init(&mut self, start_addr: usize, count: usize, block_size: usize) {
        self.block_size = block_size;
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
    pub slab_allocator: [Slab; SLAB_ALLOCATOR_COUNT],
    pub system_allocator: tlsf::TlsfHeap,
    pub slab_begin_addr: usize,
    pub slab_total_size: usize,
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
            system_allocator: tlsf::TlsfHeap::new(),
            slab_begin_addr: 0,
            slab_total_size: 0,
            allocated: 0,
            maximum: 0,
            total: 0,
        }
    }

    /// Add a range of memory [start, start+size) to the heap
    pub unsafe fn init(&mut self, start: usize, size: usize) {
        let block = crate::support::nonnull_slice_from_raw_parts(
            NonNull::new_unchecked(start as *mut u8),
            size,
        );
        self.system_allocator.insert_free_block_ptr(block);
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
                    && Self::SLAB_SIZES[allocator_index].is_multiple_of(layout.align())
                {
                    ptr = self.slab_allocator[allocator_index].allocate(layout);
                    if ptr.is_some() {
                        self.allocated += Self::SLAB_SIZES[allocator_index];
                    }
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
            self.allocated = self.allocated.saturating_sub(size);
            size
        } else {
            self.slab_allocator[allocator_index].deallocate(ptr);
            self.allocated = self
                .allocated
                .saturating_sub(Self::SLAB_SIZES[allocator_index]);
            Self::SLAB_SIZES[allocator_index]
        }
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let allocator_index = self.ptr_to_allocator(ptr.as_ptr() as usize);
        if allocator_index >= SLAB_ALLOCATOR_COUNT {
            let size = self.system_allocator.deallocate_unknown_align(ptr);
            self.allocated = self.allocated.saturating_sub(size);
            size
        } else {
            self.slab_allocator[allocator_index].deallocate(ptr);
            self.allocated = self
                .allocated
                .saturating_sub(Self::SLAB_SIZES[allocator_index]);
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
            let old_size = self.system_allocator.size_of_allocation(ptr)?;
            let new_ptr = self.system_allocator.reallocate(ptr, new_layout)?;
            let new_size = self.system_allocator.size_of_allocation(new_ptr)?;
            self.allocated = self.allocated - old_size + new_size;
            self.maximum = core::cmp::max(self.maximum, self.allocated);
            Some(new_ptr)
        } else {
            let block_size = Self::SLAB_SIZES[allocator_index];
            if new_layout.size() <= block_size {
                return Some(ptr);
            }
            let new_ptr = self.allocate(new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), block_size);
            self.deallocate(ptr, new_layout);
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
            let old_size = self.system_allocator.size_of_allocation(ptr)?;
            let new_ptr = self
                .system_allocator
                .reallocate_unknown_align(ptr, new_size)?;
            let new_size = self.system_allocator.size_of_allocation(new_ptr)?;
            self.allocated = self.allocated - old_size + new_size;
            self.maximum = core::cmp::max(self.maximum, self.allocated);
            Some(new_ptr)
        } else {
            let block_size = Self::SLAB_SIZES[allocator_index];
            if new_size <= block_size {
                return Some(ptr);
            }
            let new_layout = Layout::from_size_align_unchecked(new_size, mem::size_of::<usize>());
            let new_ptr = self.allocate(&new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), block_size);
            self.deallocate(ptr, &new_layout);
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
        log::info!("size   total  free   max    alloc ");
        log::info!("------ ------ ------ ------ ------");
        for i in 0..SLAB_ALLOCATOR_COUNT {
            if Self::SLAB_PAGE_COUNT[i] != 0 {
                log::info!(
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
const DEFAULT_MAX_TOTAL_PAGES: usize = 32;

// Dynamic slab adds a 2048-byte size class on top of the shared slab classes.
#[cfg(allocator = "slab_dynamic")]
const DYNAMIC_SLAB_ALLOCATOR_COUNT: usize = SLAB_ALLOCATOR_COUNT + 1;

#[cfg(allocator = "slab_dynamic")]
const DYNAMIC_SLAB_SIZES: [usize; DYNAMIC_SLAB_ALLOCATOR_COUNT] =
    [8, 16, 32, 64, 96, 128, 192, 256, 512, 1024, 2048];

// ── External Metadata Helper Functions ──────────────────────────────────────

/// Map page address to metadata index
#[cfg(allocator = "slab_dynamic")]
#[inline]
fn page_to_meta_index(page_addr: usize, heap_base: usize) -> usize {
    (page_addr - heap_base) / PAGE_SIZE
}

/// Get metadata for a page address
#[cfg(allocator = "slab_dynamic")]
#[inline]
unsafe fn get_page_meta(
    page_addr: usize,
    metadata: *mut PageMetadata,
    heap_base: usize,
) -> &'static mut PageMetadata {
    let idx = page_to_meta_index(page_addr, heap_base);
    &mut *metadata.add(idx)
}

// ── PageMetadata ─────────────────────────────────────────────────────────────

/// Metadata for a slab page, stored externally in SLAB_METADATA array.
/// No longer embedded in the page itself, allowing full page for data blocks.
///
/// Fields:
///   page_magic   — PAGE_MAGIC when page is owned by a DynamicSlab
///   slab_index   — index into DYNAMIC_SLAB_SIZES[] (0..DYNAMIC_SLAB_ALLOCATOR_COUNT)
///   free_blocks  — number of free blocks currently in this page
///   total_blocks — total blocks in this page (constant after init)
///   free_head    — address of first free block; 0 = empty
///   next_page    — index of next page in list; MAX_SLAB_PAGES = end
///   prev_page    — index of prev page in list; MAX_SLAB_PAGES = end
#[cfg(allocator = "slab_dynamic")]
#[repr(C)]
struct PageMetadata {
    page_magic: u32,
    slab_index: u8,
    _pad: [u8; 3],
    free_blocks: u32,
    total_blocks: u32,
    free_head: usize,
    next_page: usize,
    prev_page: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl PageMetadata {
    const fn new() -> Self {
        Self {
            page_magic: 0,
            slab_index: 0,
            _pad: [0; 3],
            free_blocks: 0,
            total_blocks: 0,
            free_head: 0,
            next_page: usize::MAX,
            prev_page: usize::MAX,
        }
    }
}

// ── Index-based List Operations ──────────────────────────────────────────────

/// Push page to front of list
#[cfg(allocator = "slab_dynamic")]
unsafe fn list_push_front(
    head_idx: &mut usize,
    page_idx: usize,
    metadata: *mut PageMetadata,
    max_pages: usize,
) {
    let meta = &mut *metadata.add(page_idx);
    meta.next_page = *head_idx;
    meta.prev_page = max_pages;

    if *head_idx != max_pages {
        (*metadata.add(*head_idx)).prev_page = page_idx;
    }
    *head_idx = page_idx;
}

/// Remove page from list
#[cfg(allocator = "slab_dynamic")]
unsafe fn list_remove(
    head_idx: &mut usize,
    page_idx: usize,
    metadata: *mut PageMetadata,
    max_pages: usize,
) {
    let meta = &*metadata.add(page_idx);
    let next = meta.next_page;
    let prev = meta.prev_page;

    if prev != max_pages {
        (*metadata.add(prev)).next_page = next;
    } else {
        *head_idx = next;
    }

    if next != max_pages {
        (*metadata.add(next)).prev_page = prev;
    }
}

/// Pop page from front of list
#[cfg(allocator = "slab_dynamic")]
unsafe fn list_pop_front(
    head_idx: &mut usize,
    metadata: *mut PageMetadata,
    max_pages: usize,
) -> Option<usize> {
    if *head_idx == max_pages {
        return None;
    }
    let page_idx = *head_idx;
    list_remove(head_idx, page_idx, metadata, max_pages);
    Some(page_idx)
}

/// Byte offset from page base where the first allocatable block starts.
/// With external metadata, the entire page is available for data blocks.
#[cfg(allocator = "slab_dynamic")]
fn page_data_offset(_block_size: usize) -> usize {
    0
}

/// Number of allocatable blocks that fit in a single PAGE_SIZE page.
/// With external metadata, we can use the full page.
#[cfg(allocator = "slab_dynamic")]
fn blocks_per_page(block_size: usize) -> usize {
    PAGE_SIZE / block_size
}

/// Check whether `ptr` lives inside a dynamically managed slab page.
///
/// Returns `Some(slab_index)` when the page's magic matches, `None` otherwise.
/// With external metadata, we look up the metadata array.
///
/// # Safety
/// The page-aligned address is always readable in kernel context.
#[cfg(allocator = "slab_dynamic")]
fn ptr_is_slab(
    ptr: usize,
    metadata: *mut PageMetadata,
    heap_base: usize,
    max_pages: usize,
) -> Option<u8> {
    let page_base = ptr & !(PAGE_SIZE - 1);
    assert!(
        heap_base != 0 && page_base >= heap_base,
        "invalid ptr {:#x}, heap_base {:#x} or page_base {:#x}",
        ptr,
        heap_base,
        page_base
    );
    unsafe {
        let page_idx = page_to_meta_index(page_base, heap_base);
        if page_idx >= max_pages {
            return None;
        }
        let meta = &*metadata.add(page_idx);
        if meta.page_magic == PAGE_MAGIC {
            Some(meta.slab_index)
        } else {
            None
        }
    }
}

// ── DynamicSlab ──────────────────────────────────────────────────────────────

#[cfg(allocator = "slab_dynamic")]
struct DynamicSlab {
    block_size: usize,
    page_list_head: usize, // Index into metadata array, max_pages = empty
    total_blocks: usize,
    free_blocks: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlab {
    const fn new() -> Self {
        DynamicSlab {
            block_size: 0,
            page_list_head: usize::MAX,
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
    unsafe fn init_page(
        &mut self,
        page_addr: usize,
        slab_index: u8,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) {
        let offset = page_data_offset(self.block_size);
        let total = blocks_per_page(self.block_size);

        // Build intrusive free list
        let mut prev_free: usize = NULL_PTR;
        for i in (0..total).rev() {
            let block_addr = page_addr + offset + i * self.block_size;
            *(block_addr as *mut usize) = prev_free;
            prev_free = block_addr;
        }

        // Get external metadata
        let meta = get_page_meta(page_addr, metadata, heap_base);
        meta.page_magic = PAGE_MAGIC;
        meta.slab_index = slab_index;
        meta._pad = [0u8; 3];
        meta.free_blocks = total as u32;
        meta.total_blocks = total as u32;
        meta.free_head = if total > 0 {
            page_addr + offset
        } else {
            NULL_PTR
        };
        meta.next_page = max_pages;
        meta.prev_page = max_pages;

        // Add to page list
        let page_idx = page_to_meta_index(page_addr, heap_base);
        if page_idx >= max_pages {
            panic!(
                "init_page: page_idx {} >= max_pages {}, page_addr={:#x}, heap_base={:#x}",
                page_idx, max_pages, page_addr, heap_base
            );
        }
        list_push_front(&mut self.page_list_head, page_idx, metadata, max_pages);
        self.total_blocks += total;
        self.free_blocks += total;
    }

    /// Add an already-initialized page back to this slab (from PagePool).
    /// The page must have been previously initialized for this slab type and be fully free.
    unsafe fn add_page(
        &mut self,
        page_addr: usize,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) {
        let meta = get_page_meta(page_addr, metadata, heap_base);
        debug_assert_eq!(
            meta.free_blocks, meta.total_blocks,
            "Page from pool must be fully free"
        );
        let page_idx = page_to_meta_index(page_addr, heap_base);
        if page_idx >= max_pages {
            panic!(
                "add_page: page_idx {} >= max_pages {}, page_addr={:#x}, heap_base={:#x}",
                page_idx, max_pages, page_addr, heap_base
            );
        }
        list_push_front(&mut self.page_list_head, page_idx, metadata, max_pages);
        self.total_blocks += meta.total_blocks as usize;
        self.free_blocks += meta.total_blocks as usize;
    }

    /// Allocate one block from the first page that has free blocks.
    /// Returns `None` if all pages are full (caller must add a new page first).
    unsafe fn allocate_block(
        &mut self,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) -> Option<NonNull<u8>> {
        let mut page_idx = self.page_list_head;
        while page_idx != max_pages {
            let meta = &*metadata.add(page_idx);
            if meta.free_blocks > 0 {
                let page_addr = heap_base + page_idx * PAGE_SIZE;
                return Some(self.pop_from_page(page_addr, metadata, heap_base));
            }
            page_idx = meta.next_page;
        }
        None
    }

    /// Pop one block from the free list of the given page.
    ///
    /// # Safety
    /// `page_addr` must be an active slab page with `free_blocks > 0`.
    unsafe fn pop_from_page(
        &mut self,
        page_addr: usize,
        metadata: *mut PageMetadata,
        heap_base: usize,
    ) -> NonNull<u8> {
        let meta = get_page_meta(page_addr, metadata, heap_base);
        let block_addr = meta.free_head;
        debug_assert_ne!(block_addr, NULL_PTR, "pop_from_page called on empty page");

        let next_free = *(block_addr as *const usize);
        meta.free_head = next_free;
        meta.free_blocks -= 1;
        self.free_blocks -= 1;

        NonNull::new_unchecked(block_addr as *mut u8)
    }

    /// Push `ptr` back onto its page's free list.
    ///
    /// Returns `(page_addr, page_is_now_fully_free)`.
    ///
    /// # Safety
    /// `ptr` must be a block previously allocated from this `DynamicSlab`.
    unsafe fn free_block(
        &mut self,
        ptr: NonNull<u8>,
        metadata: *mut PageMetadata,
        heap_base: usize,
    ) -> (usize, bool) {
        let ptr_addr = ptr.as_ptr() as usize;
        let page_addr = ptr_addr & !(PAGE_SIZE - 1);
        let meta = get_page_meta(page_addr, metadata, heap_base);

        debug_assert_eq!(meta.page_magic, PAGE_MAGIC);
        debug_assert!(
            meta.free_blocks < meta.total_blocks,
            "double-free detected at {:p}",
            ptr.as_ptr()
        );

        *(ptr.as_ptr() as *mut usize) = meta.free_head;
        meta.free_head = ptr_addr;
        meta.free_blocks += 1;
        self.free_blocks += 1;

        let fully_free = meta.free_blocks == meta.total_blocks;
        (page_addr, fully_free)
    }

    /// Unlink `page_addr` from the intrusive page list and update aggregate counters.
    ///
    /// Clears `page_magic` so `ptr_is_slab` returns `None` for this page afterwards.
    ///
    /// # Safety
    /// `page_addr` must be currently in `self`'s page list.
    unsafe fn remove_page(
        &mut self,
        page_addr: usize,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) {
        let meta = get_page_meta(page_addr, metadata, heap_base);
        let total = meta.total_blocks as usize;

        // Remove from list
        let page_idx = page_to_meta_index(page_addr, heap_base);
        list_remove(&mut self.page_list_head, page_idx, metadata, max_pages);

        self.total_blocks -= total;
        self.free_blocks -= total;
        meta.page_magic = 0;
    }
}

// ── PagePool ─────────────────────────────────────────────────────────────────

/// SLUB-style page pool: caches fully-free slab pages to reduce system pressure.
/// Uses per-slab intrusive linked lists for O(1) same-type page reuse.
#[cfg(allocator = "slab_dynamic")]
struct PagePool {
    lists: [usize; DYNAMIC_SLAB_ALLOCATOR_COUNT], // Head indices, max_pages = empty
    total_pages: usize,
    max_total_pages: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl PagePool {
    const fn new() -> Self {
        PagePool {
            lists: [usize::MAX; DYNAMIC_SLAB_ALLOCATOR_COUNT],
            total_pages: 0,
            max_total_pages: DEFAULT_MAX_TOTAL_PAGES,
        }
    }

    /// Try to release a fully-free page into the pool.
    ///
    /// # Safety
    /// `page_addr` must be PAGE_SIZE-aligned and no longer in any `DynamicSlab`'s list.
    unsafe fn release_page<S: DynamicSlabSystemAllocator>(
        &mut self,
        page_addr: usize,
        slab_index: usize,
        system_allocator: &mut S,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) {
        if self.total_pages >= self.max_total_pages {
            // Pool full - deallocate page back to system
            system_allocator.deallocate(NonNull::new_unchecked(page_addr as *mut u8));
            return;
        }

        let page_idx = page_to_meta_index(page_addr, heap_base);
        assert!(
            page_idx < max_pages,
            "addr {} page_idx {} out of bounds",
            page_addr,
            page_idx
        );
        let meta = get_page_meta(page_addr, metadata, heap_base);
        meta.slab_index = slab_index as u8;
        list_push_front(&mut self.lists[slab_index], page_idx, metadata, max_pages);
        meta.page_magic = PAGE_MAGIC; // Mark as valid slab page for reuse
        self.total_pages += 1;
    }

    /// Take one page from the pool, preferring same slab_index.
    ///
    /// # Safety
    /// Caller must immediately call `DynamicSlab::init_page` on the returned page.
    /// Returns (page_addr, needs_init): needs_init=true if page is from different slab type
    unsafe fn take_page(
        &mut self,
        slab_index: usize,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) -> Option<(usize, bool)> {
        // Try same slab_index first - no init needed
        if let Some(page_idx) = list_pop_front(&mut self.lists[slab_index], metadata, max_pages) {
            debug_assert!(page_idx < max_pages, "page_idx out of bounds");
            let addr = heap_base.checked_add(page_idx.checked_mul(PAGE_SIZE)?)?;
            self.total_pages -= 1;
            return Some((addr, false));
        }

        // Fallback: take from any other slab - needs reinit
        for i in 0..DYNAMIC_SLAB_ALLOCATOR_COUNT {
            if let Some(page_idx) = list_pop_front(&mut self.lists[i], metadata, max_pages) {
                debug_assert!(page_idx < max_pages, "page_idx out of bounds");
                let addr = heap_base.checked_add(page_idx.checked_mul(PAGE_SIZE)?)?;
                self.total_pages -= 1;
                return Some((addr, true));
            }
        }

        None
    }

    /// Reclaim up to `pages_needed` pages from the pool and return them to system.
    ///
    /// # Safety
    /// `system` must be the same allocator from which the pages were originally obtained.
    unsafe fn reclaim_to_system<S: DynamicSlabSystemAllocator>(
        &mut self,
        system_allocator: &mut S,
        pages_needed: usize,
        metadata: *mut PageMetadata,
        heap_base: usize,
        max_pages: usize,
    ) -> usize {
        let mut reclaimed = 0;

        while reclaimed < pages_needed {
            let mut found = false;
            for i in 0..DYNAMIC_SLAB_ALLOCATOR_COUNT {
                if let Some(page_idx) = list_pop_front(&mut self.lists[i], metadata, max_pages) {
                    debug_assert!(page_idx < max_pages, "page_idx out of bounds");
                    let page_addr = heap_base + page_idx * PAGE_SIZE;
                    unsafe {
                        let meta = &mut *metadata.add(page_idx);
                        meta.page_magic = 0;
                        system_allocator.deallocate(NonNull::new_unchecked(page_addr as *mut u8));
                    }
                    self.total_pages -= 1;
                    reclaimed += 1;
                    found = true;
                    break;
                }
            }
            if !found {
                break;
            }
        }
        reclaimed
    }
}

// ── DynamicSlabHeap ───────────────────────────────────────────────────────────

#[cfg(allocator = "slab_dynamic")]
type SlabStatData = [(usize, usize, usize, usize); DYNAMIC_SLAB_ALLOCATOR_COUNT];

/// Page-granularity backing allocator used by [`DynamicSlabHeap`].
///
/// Implementations may use interior locking. Every allocation returned from
/// this interface must live in the range passed to [`Self::init`], because the
/// dynamic slab uses that range to index its external page metadata.
#[cfg(allocator = "slab_dynamic")]
pub trait DynamicSlabSystemAllocator {
    /// Prepare the backing allocator for `start..start + size`.
    ///
    /// # Safety
    ///
    /// The range must remain valid and exclusively owned by the allocator.
    unsafe fn init(&mut self, start: usize, size: usize);

    fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>>;

    /// Release an allocation and return its accounting size.
    ///
    /// The returned value must equal the value that
    /// [`Self::allocation_charge`] reported for the same live allocation.
    ///
    /// # Safety
    ///
    /// `ptr` must be a live allocation returned by this allocator.
    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> usize;

    /// Return the number of bytes usable by the caller from `ptr`.
    fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize>;

    /// Return the accounting size that [`Self::deallocate`] will return for
    /// this live allocation. This may include allocator metadata or padding
    /// that is not part of the caller-usable size.
    fn allocation_charge(&self, ptr: NonNull<u8>) -> Option<usize>;

    fn get_max_free_block_size(&self) -> usize;
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlabSystemAllocator for tlsf::TlsfHeap {
    unsafe fn init(&mut self, start: usize, size: usize) {
        let block = crate::support::nonnull_slice_from_raw_parts(
            NonNull::new_unchecked(start as *mut u8),
            size,
        );
        self.insert_free_block_ptr(block);
    }

    fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        self.allocate(layout)
    }

    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> usize {
        self.deallocate_unknown_align(ptr)
    }

    fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize> {
        self.size_of_allocation(ptr)
    }

    fn allocation_charge(&self, ptr: NonNull<u8>) -> Option<usize> {
        // `TlsfHeap::size_of_allocation` returns usable payload bytes, while
        // `deallocate_unknown_align` returns the complete TLSF block size. The
        // dynamic slab uses this value for both incrementing and decrementing
        // its allocation counter, so use the same block-size accounting here.
        unsafe {
            let block = used_block_hdr_for_allocation_unknown_align(ptr)?;
            Some(block.cast::<BlockHdr>().as_ref().size & !SIZE_USED)
        }
    }

    fn get_max_free_block_size(&self) -> usize {
        self.get_max_free_block_size()
    }
}

#[cfg(allocator = "slab_dynamic")]
pub struct DynamicSlabHeap<S = tlsf::TlsfHeap> {
    slabs: [DynamicSlab; DYNAMIC_SLAB_ALLOCATOR_COUNT],
    page_pool: PagePool,
    system_allocator: S,
    allocated: usize,
    maximum: usize,
    total: usize,
    // External metadata
    metadata: *mut PageMetadata,
    heap_base: usize,
    max_pages: usize,
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlabHeap<tlsf::TlsfHeap> {
    pub const fn new() -> Self {
        Self::new_with_system_allocator(tlsf::TlsfHeap::new())
    }
}

#[cfg(allocator = "slab_dynamic")]
impl<S: DynamicSlabSystemAllocator> DynamicSlabHeap<S> {
    pub const fn new_with_system_allocator(system_allocator: S) -> Self {
        DynamicSlabHeap {
            slabs: [const { DynamicSlab::new() }; DYNAMIC_SLAB_ALLOCATOR_COUNT],
            page_pool: PagePool::new(),
            system_allocator,
            allocated: 0,
            maximum: 0,
            total: 0,
            metadata: core::ptr::null_mut(),
            heap_base: 0,
            max_pages: 0,
        }
    }

    /// Initialize the heap with the memory range `[start, start+size)`.
    ///
    /// Unlike `SlabHeap`, no memory is pre-allocated for slabs. All slab pages
    /// are fetched lazily from the system allocator on first demand.
    ///
    /// # Safety
    /// `start..start+size` must be valid, exclusively owned, writable memory.
    pub unsafe fn init(&mut self, start: usize, size: usize) {
        // Calculate metadata requirements
        self.heap_base = crate::support::align_up_size(start, PAGE_SIZE);
        self.max_pages = size / PAGE_SIZE;

        self.system_allocator.init(start, size);
        self.total = size;

        // Allocate the per-page slab metadata from the system allocator.
        let metadata_size = self.max_pages * core::mem::size_of::<PageMetadata>();
        let metadata_layout =
            Layout::from_size_align_unchecked(metadata_size, core::mem::align_of::<PageMetadata>());
        let metadata_ptr = self
            .system_allocator
            .allocate(&metadata_layout)
            .expect("Failed to allocate metadata");
        self.metadata = metadata_ptr.as_ptr() as *mut PageMetadata;

        // Initialize all metadata entries
        for i in 0..self.max_pages {
            self.metadata.add(i).write(PageMetadata::new());
        }

        // Initialize page_pool lists with max_pages as empty sentinel
        for i in 0..DYNAMIC_SLAB_ALLOCATOR_COUNT {
            self.page_pool.lists[i] = self.max_pages;
        }

        for i in 0..DYNAMIC_SLAB_ALLOCATOR_COUNT {
            self.slabs[i].page_list_head = self.max_pages;
            self.slabs[i].set_block_size(DYNAMIC_SLAB_SIZES[i]);
        }
        self.prewarm_critical_slabs();
    }

    unsafe fn prewarm_critical_slabs(&mut self) {
        const PREWARM: &[(usize, usize)] = &[(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1)];
        for &(idx, count) in PREWARM {
            for _ in 0..count {
                if let Some((page, _needs_init)) = self.acquire_page(idx) {
                    self.slabs[idx].init_page(
                        page,
                        idx as u8,
                        self.metadata,
                        self.heap_base,
                        self.max_pages,
                    );
                } else {
                    return;
                }
            }
        }
    }

    // ── Allocation ─────────────────────────────────────────────────────────

    /// Return the slab index for the given `(size, align)`.
    /// Result is `DYNAMIC_SLAB_ALLOCATOR_COUNT` when no slab can satisfy the request.
    fn layout_to_slab_index(size: usize, align: usize) -> usize {
        let min_size = core::cmp::max(size, align);
        DYNAMIC_SLAB_SIZES.partition_point(|&s| s < min_size)
    }

    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let ptr = unsafe { self.do_allocate(layout) };
        if ptr.is_some() {
            self.maximum = core::cmp::max(self.maximum, self.allocated);
        }
        ptr
    }

    unsafe fn do_allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let mut idx = Self::layout_to_slab_index(layout.size(), layout.align());

        // Slab path: try from idx upward (upsearch handles alignment mismatches on small sizes).
        while idx < DYNAMIC_SLAB_ALLOCATOR_COUNT {
            if !DYNAMIC_SLAB_SIZES[idx].is_multiple_of(layout.align()) {
                idx += 1;
                continue;
            }

            // Ensure the slab has at least one free block; add a new page if needed.
            if self.slabs[idx].free_blocks == 0 {
                if let Some((page_addr, needs_init)) = self.acquire_page(idx) {
                    if needs_init {
                        self.slabs[idx].init_page(
                            page_addr,
                            idx as u8,
                            self.metadata,
                            self.heap_base,
                            self.max_pages,
                        );
                    } else {
                        self.slabs[idx].add_page(
                            page_addr,
                            self.metadata,
                            self.heap_base,
                            self.max_pages,
                        );
                    }
                } else {
                    // Cannot acquire page, fallback to system for this allocation
                    break;
                }
            }

            let ptr = self.slabs[idx]
                .allocate_block(self.metadata, self.heap_base, self.max_pages)
                .unwrap();
            self.allocated += DYNAMIC_SLAB_SIZES[idx];
            return Some(ptr);
        }

        // Requests larger than 2048 bytes (or with a larger alignment) are
        // forwarded to the page-granularity system allocator.
        let ptr = if let Some(ptr) = self.system_allocator.allocate(layout) {
            ptr
        } else {
            // System allocation failed, return cached pages and retry.
            self.reclaim_page_pool();
            self.system_allocator.allocate(layout)?
        };
        self.allocated += self.system_allocator.allocation_charge(ptr)?;
        Some(ptr)
    }

    /// Obtain a fresh PAGE_SIZE page: first try the pool, then system.
    /// Returns (page_addr, needs_init): needs_init=false if page is already initialized for this slab.
    unsafe fn acquire_page(&mut self, slab_index: usize) -> Option<(usize, bool)> {
        if let Some((page, needs_init)) =
            self.page_pool
                .take_page(slab_index, self.metadata, self.heap_base, self.max_pages)
        {
            return Some((page, needs_init));
        }
        let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
        if let Some(ptr) = self.system_allocator.allocate(&page_layout) {
            return Some((ptr.as_ptr() as usize, true));
        }
        // system allocation failed, try reclaiming all pages from pool
        self.reclaim_page_pool();
        self.system_allocator
            .allocate(&page_layout)
            .map(|ptr| (ptr.as_ptr() as usize, true))
    }

    // ── Deallocation ───────────────────────────────────────────────────────

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, _layout: &Layout) -> usize {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr, self.metadata, self.heap_base, self.max_pages)
        {
            self.free_slab_block(ptr, slab_idx as usize)
        } else {
            let size = self.system_allocator.deallocate(ptr);
            self.allocated -= size;
            size
        }
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr, self.metadata, self.heap_base, self.max_pages)
        {
            self.free_slab_block(ptr, slab_idx as usize)
        } else {
            let size = self.system_allocator.deallocate(ptr);
            self.allocated -= size;
            size
        }
    }

    /// Free a slab block and, if the page becomes fully empty, either pool or
    /// return the page to the system allocator.
    unsafe fn free_slab_block(&mut self, ptr: NonNull<u8>, idx: usize) -> usize {
        let (page_addr, page_empty) =
            self.slabs[idx].free_block(ptr, self.metadata, self.heap_base);
        self.allocated -= DYNAMIC_SLAB_SIZES[idx];

        if page_empty {
            self.slabs[idx].remove_page(page_addr, self.metadata, self.heap_base, self.max_pages);
            self.page_pool.release_page(
                page_addr,
                idx,
                &mut self.system_allocator,
                self.metadata,
                self.heap_base,
                self.max_pages,
            );
        }
        DYNAMIC_SLAB_SIZES[idx]
    }

    // ── Reallocation ───────────────────────────────────────────────────────

    pub unsafe fn reallocate(
        &mut self,
        ptr: NonNull<u8>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr, self.metadata, self.heap_base, self.max_pages)
        {
            let idx = slab_idx as usize;
            if new_layout.size() <= DYNAMIC_SLAB_SIZES[idx]
                && DYNAMIC_SLAB_SIZES[idx].is_multiple_of(new_layout.align())
            {
                return Some(ptr); // fits in existing block
            }
            let new_ptr = self.allocate(new_layout)?;
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.as_ptr(),
                DYNAMIC_SLAB_SIZES[idx].min(new_layout.size()),
            );
            // Use deallocate_unknown_align: for slab blocks, deallocate() ignores
            // the layout argument (routes via ptr_is_slab), so this is cleaner.
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
        } else {
            let old_size = self.system_allocator.size_of_allocation(ptr)?;
            if Self::layout_to_slab_index(new_layout.size(), new_layout.align())
                == DYNAMIC_SLAB_ALLOCATOR_COUNT
                && new_layout.size() <= old_size
                && (ptr.as_ptr() as usize).is_multiple_of(new_layout.align())
            {
                return Some(ptr);
            }
            let new_ptr = self.allocate(new_layout)?;
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.as_ptr(),
                old_size.min(new_layout.size()),
            );
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
        }
    }

    pub unsafe fn reallocate_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let ptr_addr = ptr.as_ptr() as usize;
        if let Some(slab_idx) = ptr_is_slab(ptr_addr, self.metadata, self.heap_base, self.max_pages)
        {
            let idx = slab_idx as usize;
            if new_size <= DYNAMIC_SLAB_SIZES[idx] {
                return Some(ptr);
            }
            let new_layout =
                Layout::from_size_align(new_size, core::mem::size_of::<usize>()).ok()?;
            let new_ptr = self.allocate(&new_layout)?;
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.as_ptr(),
                DYNAMIC_SLAB_SIZES[idx].min(new_size),
            );
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
        } else {
            let old_size = self.system_allocator.size_of_allocation(ptr)?;
            let new_layout =
                Layout::from_size_align(new_size, core::mem::size_of::<usize>()).ok()?;
            if Self::layout_to_slab_index(new_size, new_layout.align())
                == DYNAMIC_SLAB_ALLOCATOR_COUNT
                && new_size <= old_size
            {
                return Some(ptr);
            }
            let new_ptr = self.allocate(&new_layout)?;
            core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size.min(new_size));
            self.deallocate_unknown_align(ptr);
            Some(new_ptr)
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
        if let Some(slab_idx) = ptr_is_slab(ptr_addr, self.metadata, self.heap_base, self.max_pages)
        {
            Some(DYNAMIC_SLAB_SIZES[slab_idx as usize])
        } else {
            self.system_allocator.size_of_allocation(ptr)
        }
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let sys_free = self.system_allocator.get_max_free_block_size();
        for i in (0..DYNAMIC_SLAB_ALLOCATOR_COUNT).rev() {
            if self.slabs[i].free_blocks > 0 {
                return core::cmp::max(sys_free, DYNAMIC_SLAB_SIZES[i]);
            }
        }
        sys_free
    }

    // ── System allocator memory pressure ──────────────────────────────────

    /// Reclaim pages from the pool when system memory pressure is detected.
    pub fn check_memory_pressure(&mut self) {
        let max_free = self.system_allocator.get_max_free_block_size();
        if max_free < MEMORY_PRESSURE_THRESHOLD {
            let pages_needed = (MEMORY_PRESSURE_THRESHOLD - max_free) / PAGE_SIZE + 1;
            unsafe {
                self.page_pool.reclaim_to_system(
                    &mut self.system_allocator,
                    pages_needed,
                    self.metadata,
                    self.heap_base,
                    self.max_pages,
                );
            }
        }
    }

    /// Reclaim all pages from the page pool back to the system allocator.
    /// Used in tests for accurate memory leak detection.
    pub fn reclaim_page_pool(&mut self) {
        unsafe {
            self.page_pool.reclaim_to_system(
                &mut self.system_allocator,
                usize::MAX,
                self.metadata,
                self.heap_base,
                self.max_pages,
            );
        }
    }

    pub fn get_slab_stat(&self) -> (SlabStatData, usize, usize) {
        let mut data = [(0usize, 0usize, 0usize, 0usize); DYNAMIC_SLAB_ALLOCATOR_COUNT];
        for (i, item) in data.iter_mut().enumerate() {
            let bpp = blocks_per_page(DYNAMIC_SLAB_SIZES[i]);
            let pages = self.slabs[i].total_blocks.div_ceil(bpp);
            *item = (
                DYNAMIC_SLAB_SIZES[i],
                pages,
                self.slabs[i].total_blocks,
                self.slabs[i].free_blocks,
            );
        }
        (
            data,
            self.page_pool.total_pages,
            self.page_pool.max_total_pages,
        )
    }
}
