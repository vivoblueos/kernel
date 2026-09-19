// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! Lock-free core of the physical-page buddy allocator.
//!
//! The caller owns synchronization, physical-address translation, metadata
//! placement, and the lifetime of the metadata buffer.

use blueos_infra::{
    impl_simple_intrusive_adapter,
    list::typed_ilist::{List as Ilist, ListHead as IlistHead},
};
use core::{alloc::Layout, ops::Range, ptr::NonNull};

/// Base-two logarithm of the page size.
pub const PAGE_SHIFT: usize = 12;
/// Size of one page in bytes.
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
/// Largest allocation order supported by the allocator.
pub const MAX_ORDER: usize = 11;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PageState {
    Unavailable,
    Allocated,
    Free,
}

impl_simple_intrusive_adapter!(PageListNodeAdapter, PageDescriptor, list_node);

/// Private metadata for one page frame.
///
/// Kernel-specific page state must not be added here. This descriptor only
/// contains fields required by the buddy algorithm.
#[repr(C)]
struct PageDescriptor {
    list_node: IlistHead<PageDescriptor, PageListNodeAdapter>,
    pfn: usize,
    order: u8,
    state: PageState,
}

impl PageDescriptor {
    const fn new(pfn: usize) -> Self {
        Self {
            list_node: IlistHead::new(),
            pfn,
            order: 0,
            state: PageState::Unavailable,
        }
    }
}

// Physical memory layout of buddy allocator
// ============================================================================
//
//   mem_start (e.g. 0x4000_0000)
//   +-- kernel image (.text .rodata .data .bss)
//   +-- __heap_start -- __heap_end (a small memory region reserved by link.x)
//   |
//   |    +--------------------------------------------------------------+
//   |    |  struct Page[total_pages]  <-- page descriptor array         |
//   |    |  each page 32-48 bytes, flags: FREE/RESERVED/order/refcount  |
//   |    +--------------------------------------------------------------+
//   |
//   +--> start_pfn (first usable page after metadata)
//        |
//        |  Usable region is split into the largest possible buddy-aligned
//        |  blocks (up to MAX_ORDER=11, 8 MB). The head page of each block
//        |  has FREE=1 and its actual order; all other pages have FREE=0
//        |  (invalid). The first block's order may be < MAX_ORDER if
//        |  start_pfn is not aligned to a MAX_ORDER boundary.
//        |
//        |  +----------+  +----------+         +----------+  +----------+
//        |  | pfn=N    |  | pfn=N+1  |  ...    | pfn=M    |  | pfn=M+1  |  ...
//        |  | FREE=1   |  | FREE=0   |         | FREE=1   |  | FREE=0   |
//        |  | order=11 |  | (invalid)|         | order=11 |  | (invalid)|
//        |  +----------+  +----------+         +----------+  +----------+
//        |       ^ chunk 0 head                     ^ chunk 1 head
//        |
//        |           ... all pages in between FREE=0 ...
//        |
//        |  +----------+         +----------+
//        |  | pfn=P    |  ...    | pfn=end  |
//        |  | FREE=1   |         | FREE=0   |
//        |  | order=K  |         | (invalid)|
//        |  +----------+         +----------+
//        |       ^ last chunk head (order=K < 11 if size < 8 MB)
//        |
//        +--> each MAX_ORDER chunk spans 2048 pages; only the head page
//             has valid flags.
//
//   mem_end (e.g. 0x4800_0000)
// ============================================================================

/// Calculate the smallest order whose block can contain `size` bytes.
#[inline]
pub const fn order_of_size(size: usize) -> usize {
    if size <= PAGE_SIZE {
        0
    } else {
        // ceil(size / PAGE_SIZE) needs one more bit than
        // floor((size - 1) / PAGE_SIZE).
        (usize::BITS - ((size - 1) >> PAGE_SHIFT).leading_zeros()) as usize
    }
}

/// An opaque page frame returned by [`BuddyAllocator`].
///
/// The contained PFN is relative to the physical base selected by the caller.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PageFrame(usize);

impl PageFrame {
    /// Return the page-frame number relative to the caller's physical base.
    pub const fn pfn(self) -> usize {
        self.0
    }
}

/// Initialization failures for [`BuddyAllocator`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuddyInitError {
    /// The allocator has already been initialized.
    AlreadyInitialized,
    /// At least one physical page is required.
    ZeroPages,
    /// The descriptor-array layout cannot be represented by [`Layout`].
    MetadataLayoutOverflow,
    /// The supplied descriptor buffer does not meet its alignment requirement.
    MetadataMisaligned,
    /// The supplied descriptor buffer is smaller than the required layout.
    MetadataTooSmall {
        /// Required descriptor bytes.
        required: usize,
        /// Supplied descriptor bytes.
        provided: usize,
    },
    /// The manageable PFN range is reversed or exceeds `total_pages`.
    InvalidManageableRange,
}

/// Page statistics for a buddy allocator instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// Memory statistics reported by the buddy allocator.
///
/// Fields:
/// - `total_pages`: All physical pages represented by the descriptor buffer.
/// - `free_pages`: Pages currently available for allocation.
/// - `used_pages`: Manageable pages currently allocated.
/// - `reserved_pages`: Pages outside the caller-provided manageable range.
pub struct BuddyMemoryInfo {
    pub total_pages: usize,
    pub free_pages: usize,
    pub used_pages: usize,
    pub reserved_pages: usize,
}

/// Unsynchronized buddy allocator for page-frame numbers.
///
/// Fields:
/// - `free_lists`: Free lists indexed by order (0..=MAX_ORDER). Each list holds free blocks of size 2^order pages.
/// - `pages`: Pointer to the base of the page-descriptor array.
/// - `total_pages`: Total number of physical pages this allocator covers.
/// - `manageable_start`: Index of the first page that the allocator can hand out (inclusive).
/// - `manageable_end`: Index of the first page past the manageable region (exclusive).
/// - `initialized`: Whether `init` has been called successfully.
pub struct BuddyAllocator {
    free_lists: [Ilist<PageDescriptor, PageListNodeAdapter>; MAX_ORDER + 1],
    pages: *mut PageDescriptor,
    total_pages: usize,
    manageable_start: usize,
    manageable_end: usize,
    initialized: bool,
}

impl BuddyAllocator {
    /// Create an uninitialized allocator.
    pub const fn new() -> Self {
        Self {
            free_lists: [const { Ilist::new() }; MAX_ORDER + 1],
            pages: core::ptr::null_mut(),
            total_pages: 0,
            manageable_start: 0,
            manageable_end: 0,
            initialized: false,
        }
    }

    /// Return the descriptor-buffer layout for `total_pages` physical pages.
    pub fn metadata_layout(total_pages: usize) -> Result<Layout, BuddyInitError> {
        if total_pages == 0 {
            return Err(BuddyInitError::ZeroPages);
        }
        // Fails if the descriptor array size overflows or exceeds Layout's maximum size.
        Layout::array::<PageDescriptor>(total_pages)
            .map_err(|_| BuddyInitError::MetadataLayoutOverflow)
    }

    /// Initialize the allocator over a caller-selected PFN range.
    ///
    /// The range outside `manageable_pfns` is represented in statistics as
    /// reserved and is never placed on a free list.
    ///
    /// # Safety
    ///
    /// - `metadata..metadata + metadata_len` must be valid, writable, and
    ///   exclusively owned for the entire lifetime of this allocator.
    /// - The buffer must not overlap memory that can be returned by this
    ///   allocator.
    /// - No references into the buffer may exist when this method is called.
    /// - `self` must remain at a stable address after initialization because
    ///   the intrusive free-list sentinels contain self-referential pointers.
    pub unsafe fn init(
        &mut self,
        metadata_ptr: NonNull<u8>,
        metadata_len: usize,
        total_pages: usize,
        manageable_pfns: Range<usize>,
    ) -> Result<(), BuddyInitError> {
        if self.initialized {
            return Err(BuddyInitError::AlreadyInitialized);
        }

        let layout = Self::metadata_layout(total_pages)?;
        if manageable_pfns.start > manageable_pfns.end || manageable_pfns.end > total_pages {
            return Err(BuddyInitError::InvalidManageableRange);
        }
        if (metadata_ptr.as_ptr() as usize) & (layout.align() - 1) != 0 {
            return Err(BuddyInitError::MetadataMisaligned);
        }
        if metadata_len < layout.size() {
            return Err(BuddyInitError::MetadataTooSmall {
                required: layout.size(),
                provided: metadata_len,
            });
        }

        for list in self.free_lists.iter_mut() {
            let initialized = list.init();
            debug_assert!(initialized);
        }

        self.pages = metadata_ptr.as_ptr().cast::<PageDescriptor>();
        self.total_pages = total_pages;
        self.manageable_start = manageable_pfns.start;
        self.manageable_end = manageable_pfns.end;

        for pfn in 0..total_pages {
            self.pages.add(pfn).write(PageDescriptor::new(pfn));
        }

        let mut pfn = self.manageable_start;
        while pfn < self.manageable_end {
            let remaining = self.manageable_end - pfn;
            let max_order = MAX_ORDER.min((usize::BITS - 1 - remaining.leading_zeros()) as usize);
            let order = (0..=max_order)
                .rev()
                .find(|&candidate| pfn % (1 << candidate) == 0)
                .expect("order zero always satisfies buddy alignment");
            let page = &mut *self.page_ptr(pfn);
            page.state = PageState::Free;
            page.order = order as u8;
            self.free_lists[order]
                .push(page)
                .expect("new free block must be detached");
            pfn += 1 << order;
        }

        self.initialized = true;
        Ok(())
    }

    /// Allocate `2^order` contiguous pages.
    pub fn alloc_pages(&mut self, order: usize) -> Option<PageFrame> {
        self.alloc_pages_from(order, order)
    }

    /// Allocate `2^order` contiguous pages aligned to `2^align_order` pages.
    pub fn alloc_pages_aligned(&mut self, order: usize, align_order: usize) -> Option<PageFrame> {
        self.alloc_pages_from(order, order.max(align_order))
    }

    fn alloc_pages_from(&mut self, order: usize, search_order: usize) -> Option<PageFrame> {
        debug_assert!(self.initialized);
        if !self.initialized || order > MAX_ORDER || search_order > MAX_ORDER {
            return None;
        }

        for candidate_order in search_order..=MAX_ORDER {
            let pfn = match self.free_lists[candidate_order].front() {
                Some(page) => page.pfn,
                None => continue,
            };
            let page_ptr = self.page_ptr(pfn);
            let detached = unsafe { IlistHead::detach(&mut (*page_ptr).list_node) };
            debug_assert!(detached);
            debug_assert_eq!(unsafe { (*page_ptr).state }, PageState::Free);
            debug_assert_eq!(pfn & ((1 << candidate_order) - 1), 0);

            let mut current_order = candidate_order;
            while current_order > order {
                current_order -= 1;
                let buddy_pfn = pfn ^ (1 << current_order);
                debug_assert_eq!(buddy_pfn, pfn + (1 << current_order));
                let buddy = unsafe { &mut *self.page_ptr(buddy_pfn) };
                buddy.state = PageState::Free;
                buddy.order = current_order as u8;
                self.free_lists[current_order]
                    .push(buddy)
                    .expect("split buddy must be detached");
            }

            let page = unsafe { &mut *page_ptr };
            page.state = PageState::Allocated;
            page.order = order as u8;
            return Some(PageFrame(pfn));
        }

        None
    }

    /// Release a block previously returned by this allocator.
    ///
    /// # Safety
    ///
    /// `frame` must still denote the head of a live allocation from this
    /// allocator, and `order` must equal the order used to allocate it. The
    /// allocation must be released exactly once.
    pub unsafe fn free_pages(&mut self, frame: PageFrame, order: usize) {
        let pfn = frame.pfn();
        debug_assert!(self.initialized, "free on an uninitialized buddy");
        debug_assert!(order <= MAX_ORDER, "free order exceeds MAX_ORDER");
        debug_assert!(
            pfn >= self.manageable_start && pfn < self.manageable_end,
            "free PFN lies outside the manageable range"
        );
        if !self.initialized
            || order > MAX_ORDER
            || pfn < self.manageable_start
            || pfn >= self.manageable_end
        {
            return;
        }

        debug_assert_eq!(pfn & ((1 << order) - 1), 0, "frame is not a block head");
        let mut current_page = &mut *self.page_ptr(pfn);
        debug_assert_eq!(
            current_page.state,
            PageState::Allocated,
            "frame is not currently allocated"
        );
        debug_assert_eq!(
            current_page.order as usize, order,
            "free order differs from allocation order"
        );
        if pfn & ((1 << order) - 1) != 0
            || current_page.state != PageState::Allocated
            || current_page.order as usize != order
        {
            return;
        }

        let mut current_order = order;
        current_page.state = PageState::Free;

        while current_order < MAX_ORDER {
            let buddy_pfn = current_page.pfn ^ (1 << current_order);
            if buddy_pfn < self.manageable_start || buddy_pfn >= self.manageable_end {
                break;
            }

            let buddy = &mut *self.page_ptr(buddy_pfn);
            if buddy.state != PageState::Free || buddy.order as usize != current_order {
                break;
            }

            let detached = IlistHead::detach(&mut buddy.list_node);
            debug_assert!(detached);
            if buddy_pfn < current_page.pfn {
                current_page.state = PageState::Unavailable;
                current_page.order = 0;
                current_page = buddy;
            } else {
                buddy.state = PageState::Unavailable;
                buddy.order = 0;
            }
            current_order += 1;
            current_page.state = PageState::Free;
            current_page.order = current_order as u8;
        }

        self.free_lists[current_order]
            .push(current_page)
            .expect("coalesced block must be detached");
    }

    /// Release a block by its caller-visible PFN.
    ///
    /// # Safety
    ///
    /// `pfn` must identify the head of a live allocation from this allocator,
    /// `order` must equal its allocation order, and the block must be released
    /// exactly once.
    pub unsafe fn free_pages_pfn(&mut self, pfn: usize, order: usize) {
        self.free_pages(PageFrame(pfn), order);
    }

    /// Return current page accounting information.
    pub fn memory_info(&self) -> BuddyMemoryInfo {
        if !self.initialized {
            return BuddyMemoryInfo {
                total_pages: 0,
                free_pages: 0,
                used_pages: 0,
                reserved_pages: 0,
            };
        }

        let mut free_pages = 0;
        for order in 0..=MAX_ORDER {
            free_pages += self.free_lists[order].iter().count() * (1 << order);
        }
        let manageable_pages = self.manageable_end - self.manageable_start;
        let reserved_pages = self.total_pages - manageable_pages;

        BuddyMemoryInfo {
            total_pages: self.total_pages,
            free_pages,
            used_pages: manageable_pages.saturating_sub(free_pages),
            reserved_pages,
        }
    }

    fn page_ptr(&self, pfn: usize) -> *mut PageDescriptor {
        debug_assert!(pfn < self.total_pages);
        unsafe { self.pages.add(pfn) }
    }
}

impl Default for BuddyAllocator {
    fn default() -> Self {
        Self::new()
    }
}
