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

//! Raw metadata core for a heap backed by owned virtual page ranges.
//!
//! The caller acquires pages outside its heap lock and publishes them here. This
//! module never obtains pages, performs payload initialization, or releases pages.

mod metadata;
mod slab;

use core::{alloc::Layout, ptr::NonNull};
use metadata::Kind;
pub use metadata::{Area, AreaIndex};

pub const PAGE_SIZE: usize = 4096;
pub const CLASS_SIZES: [usize; 8] = [8, 16, 32, 64, 128, 256, 512, 1024];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassId(u8);

impl ClassId {
    pub fn size(self) -> usize {
        CLASS_SIZES[self.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PageRequest {
    pub pages: usize,
    pub align: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationPlan {
    Slab(ClassId),
    Pages(PageRequest),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeapError {
    InvalidGeometry,
    InvalidRequest,
    OutOfWindow,
    Conflict,
    NotAllocated,
    InteriorPointer,
    LayoutMismatch,
    CorruptMetadata,
}

pub fn classify(layout: Layout) -> Result<AllocationPlan, HeapError> {
    if layout.size() == 0 {
        return Err(HeapError::InvalidRequest);
    }
    let required = layout.size().max(layout.align());
    if let Some(index) = CLASS_SIZES.iter().position(|size| *size >= required) {
        return Ok(AllocationPlan::Slab(ClassId(index as u8)));
    }
    let pages = layout
        .size()
        .checked_add(PAGE_SIZE - 1)
        .ok_or(HeapError::InvalidRequest)?
        / PAGE_SIZE;
    Ok(AllocationPlan::Pages(PageRequest {
        pages,
        align: layout.align().max(PAGE_SIZE),
    }))
}

#[derive(Clone, Copy, Debug)]
pub struct PageSpan {
    start: NonNull<u8>,
    pages: usize,
    area: Option<NonNull<Area>>,
}

impl PartialEq for PageSpan {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.pages == other.pages
    }
}
impl Eq for PageSpan {}

impl PageSpan {
    /// Describes a nonempty, page-aligned run without taking ownership of it.
    ///
    /// # Safety
    /// The pointer must retain the provenance needed to access any owned pages
    /// in the run. This descriptor does not make the described memory writable.
    pub unsafe fn new(start: NonNull<u8>, pages: usize) -> Result<Self, HeapError> {
        validate_geometry(start, pages)?;
        Ok(Self {
            start,
            pages,
            area: None,
        })
    }

    /// Attach stable metadata exclusively owned by this page allocation.
    ///
    /// # Safety
    /// The area must describe exactly this span and outlive all heap/index uses.
    /// It must not already belong to an object heap. The source removes its own
    /// reservation only after the heap has detached the descriptor.
    pub unsafe fn with_area(mut self, area: NonNull<Area>) -> Result<Self, HeapError> {
        if area.as_ref().start != self.start.as_ptr().addr()
            || area.as_ref().end != self.start.as_ptr().addr() + self.byte_len()
        {
            return Err(HeapError::InvalidGeometry);
        }
        area.as_ref().attach(self.start);
        self.area = Some(area);
        Ok(self)
    }

    pub fn area(self) -> Option<NonNull<Area>> {
        self.area
    }

    pub fn start(self) -> NonNull<u8> {
        self.start
    }
    pub fn pages(self) -> usize {
        self.pages
    }
    pub fn byte_len(self) -> usize {
        self.pages * PAGE_SIZE
    }
}

#[derive(Clone, Copy)]
pub struct PageWindow {
    base: NonNull<u8>,
    pages: usize,
}

impl PageWindow {
    /// Describes a page-address window, which may include unavailable gaps.
    ///
    /// # Safety
    /// The base pointer must retain provenance for the pages that will be used.
    /// Neither constructing nor sharing a window permits accessing reserved or
    /// unowned pages, or accessing metadata without an exclusive heap borrow.
    pub unsafe fn new(base: NonNull<u8>, pages: usize) -> Result<Self, HeapError> {
        validate_geometry(base, pages)?;
        Ok(Self { base, pages })
    }

    pub fn base(self) -> NonNull<u8> {
        self.base
    }
    pub fn pages(self) -> usize {
        self.pages
    }

    pub fn span(self, first: usize, pages: usize) -> Result<PageSpan, HeapError> {
        let end = first.checked_add(pages).ok_or(HeapError::OutOfWindow)?;
        if end > self.pages {
            return Err(HeapError::OutOfWindow);
        }
        // wrapping_add preserves provenance and does not assert that gaps in
        // this address window belong to a single allocated Rust object.
        let start = self.base.as_ptr().wrapping_add(first * PAGE_SIZE);
        unsafe {
            PageSpan::new(
                NonNull::new(start).ok_or(HeapError::InvalidGeometry)?,
                pages,
            )
        }
    }

    /// Returns the covering page for either a page or an object address.
    pub fn index_of(self, ptr: NonNull<u8>) -> Result<usize, HeapError> {
        let offset = ptr
            .as_ptr()
            .addr()
            .checked_sub(self.base.as_ptr().addr())
            .ok_or(HeapError::OutOfWindow)?;
        if offset >= self.pages * PAGE_SIZE {
            return Err(HeapError::OutOfWindow);
        }
        Ok(offset / PAGE_SIZE)
    }
}

// These types only describe addresses. Sharing them does not grant access to
// payloads or metadata; metadata mutations still require &mut PageHeap.
unsafe impl Send for PageWindow {}
unsafe impl Sync for PageWindow {}
unsafe impl Send for PageSpan {}
unsafe impl Sync for PageSpan {}

fn validate_geometry(base: NonNull<u8>, pages: usize) -> Result<(), HeapError> {
    let bytes = pages
        .checked_mul(PAGE_SIZE)
        .ok_or(HeapError::InvalidGeometry)?;
    if pages == 0
        || base.as_ptr().addr() & (PAGE_SIZE - 1) != 0
        || base.as_ptr().addr().checked_add(bytes).is_none()
    {
        return Err(HeapError::InvalidGeometry);
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Allocation {
    pub ptr: NonNull<u8>,
    pub capacity: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationKind {
    Slab(ClassId),
    Large,
}

#[derive(Clone, Copy, Debug)]
pub struct AllocationInfo {
    pub kind: AllocationKind,
    pub requested_size: Option<usize>,
    pub capacity: usize,
    pub align: usize,
    pub span: PageSpan,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct HeapStats {
    pub slab_pages: usize,
    pub large_pages: usize,
    pub backing_bytes: usize,
    pub live_objects: usize,
    pub charged_bytes: usize,
    pub peak_charged_bytes: usize,
}

#[must_use = "detached physical pages must be returned to their source"]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReleaseAction {
    None,
    Pages(PageSpan),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SlabCommit {
    Inserted(Allocation),
    Existing(Allocation),
}

pub struct PageHeap {
    window: PageWindow,
    areas: AreaIndex<0>,
    stats: HeapStats,
    partial: [usize; 8],
}

impl PageHeap {
    /// Create an empty heap without allocating metadata proportional to VA size.
    ///
    /// # Safety
    /// Sources retain writable backing and stable Area metadata for every
    /// committed span until it is detached by free.
    pub unsafe fn new(window: PageWindow) -> Result<Self, HeapError> {
        Ok(Self {
            window,
            areas: AreaIndex::new(),
            stats: HeapStats::default(),
            partial: [usize::MAX; 8],
        })
    }

    fn candidate(&self, span: PageSpan) -> Result<NonNull<Area>, HeapError> {
        self.window.index_of(span.start)?;
        let end = span
            .start
            .as_ptr()
            .addr()
            .checked_add(span.byte_len())
            .ok_or(HeapError::OutOfWindow)?;
        if end > self.window.base.as_ptr().addr() + self.window.pages * PAGE_SIZE {
            return Err(HeapError::OutOfWindow);
        }
        if self.areas.overlaps(span.start.as_ptr().addr(), end) {
            return Err(HeapError::Conflict);
        }
        let area = span.area.ok_or(HeapError::InvalidGeometry)?;
        unsafe {
            if area.as_ref().start != span.start.as_ptr().addr()
                || area.as_ref().end != end
                || !area.as_ref().detached()
            {
                return Err(HeapError::Conflict);
            }
        }
        Ok(area)
    }

    pub fn stats(&self) -> HeapStats {
        self.stats
    }

    /// Committed free slab slots; unowned window pages are not heap storage.
    pub fn largest_free_slot(&self) -> usize {
        self.partial
            .iter()
            .rposition(|index| *index != usize::MAX)
            .map_or(0, |index| CLASS_SIZES[index])
    }

    /// Publishes an exclusively owned run without adding an in-band header.
    ///
    /// # Safety
    /// The caller exclusively owns all pages in the run and must retain their
    /// ownership after success until this heap returns the run from `free`.
    /// The run must be virtually contiguous and writable for its entire size.
    pub unsafe fn commit_large(
        &mut self,
        span: PageSpan,
        layout: Layout,
    ) -> Result<Allocation, HeapError> {
        if span.start.as_ptr().addr() & (PAGE_SIZE - 1) != 0 {
            return Err(HeapError::InvalidGeometry);
        }
        let area = self.candidate(span)?;
        if layout.size() == 0
            || layout.size() > span.byte_len()
            || span.start.as_ptr().addr() & (layout.align() - 1) != 0
        {
            return Err(HeapError::InvalidRequest);
        }
        let mut stats = self.stats;
        stats.large_pages = stats
            .large_pages
            .checked_add(span.pages)
            .ok_or(HeapError::InvalidRequest)?;
        stats.backing_bytes = stats
            .backing_bytes
            .checked_add(span.byte_len())
            .ok_or(HeapError::InvalidRequest)?;
        stats.live_objects = stats
            .live_objects
            .checked_add(1)
            .ok_or(HeapError::InvalidRequest)?;
        stats.charged_bytes = stats
            .charged_bytes
            .checked_add(span.byte_len())
            .ok_or(HeapError::InvalidRequest)?;
        stats.peak_charged_bytes = stats.peak_charged_bytes.max(stats.charged_bytes);
        self.areas.insert(area)?;
        area.as_ref().set_kind(Kind::Large(layout));
        self.stats = stats;
        Ok(Allocation {
            ptr: span.start,
            capacity: span.byte_len(),
        })
    }

    pub fn allocation_info(&self, ptr: NonNull<u8>) -> Result<AllocationInfo, HeapError> {
        let node = self
            .areas
            .find(ptr.as_ptr().addr())
            .ok_or(HeapError::NotAllocated)?;
        let area = unsafe { node.as_ref() };
        let kind = unsafe { area.kind() };
        let span = unsafe { Area::span(node) };
        let layout = match kind {
            Kind::Slab(class) => {
                return self.slab_info(self.window.index_of(span.start)?, ptr, class)
            }
            Kind::Large(layout) => layout,
            Kind::Empty => return Err(HeapError::CorruptMetadata),
        };
        if ptr != span.start {
            return Err(HeapError::InteriorPointer);
        }
        Ok(AllocationInfo {
            kind: AllocationKind::Large,
            requested_size: Some(layout.size()),
            capacity: span.byte_len(),
            align: layout.align(),
            span,
        })
    }

    /// Attempts to retain an allocation without changing its backing pages.
    ///
    /// # Safety
    /// `ptr` must retain its provenance and the caller must exclusively own
    /// the allocation for the duration of the resize.
    pub unsafe fn try_reuse(
        &mut self,
        ptr: NonNull<u8>,
        old: Option<Layout>,
        new: Layout,
    ) -> Result<bool, HeapError> {
        let info = self.allocation_info(ptr)?;
        validate_original_layout(info, old)?;
        if new.size() == 0 {
            return Err(HeapError::InvalidRequest);
        }
        if new.size() > info.capacity || ptr.as_ptr().addr() & (new.align() - 1) != 0 {
            return Ok(false);
        }
        if let AllocationKind::Slab(class) = info.kind {
            if new.align() > class.size() {
                return Ok(false);
            }
        } else {
            let node = info.span.area.ok_or(HeapError::CorruptMetadata)?;
            node.as_ref().set_kind(Kind::Large(new));
        }
        Ok(true)
    }

    /// Validates and detaches a large run. The caller returns detached pages to
    /// their source after releasing any heap lock.
    ///
    /// # Safety
    /// On success no payload access may remain, and the caller must honor the
    /// returned release action. `ptr` must retain its original provenance.
    pub unsafe fn free(
        &mut self,
        ptr: NonNull<u8>,
        layout: Option<Layout>,
    ) -> Result<ReleaseAction, HeapError> {
        let info = self.allocation_info(ptr)?;
        validate_original_layout(info, layout)?;
        if let AllocationKind::Slab(_) = info.kind {
            return self.free_slab(ptr, info);
        }
        let mut stats = self.stats;
        stats.large_pages = stats
            .large_pages
            .checked_sub(info.span.pages)
            .ok_or(HeapError::CorruptMetadata)?;
        stats.backing_bytes = stats
            .backing_bytes
            .checked_sub(info.capacity)
            .ok_or(HeapError::CorruptMetadata)?;
        stats.live_objects = stats
            .live_objects
            .checked_sub(1)
            .ok_or(HeapError::CorruptMetadata)?;
        stats.charged_bytes = stats
            .charged_bytes
            .checked_sub(info.capacity)
            .ok_or(HeapError::CorruptMetadata)?;
        let node = self
            .areas
            .remove(info.span.start.as_ptr().addr())
            .ok_or(HeapError::CorruptMetadata)?;
        node.as_ref().set_kind(Kind::Empty);
        self.stats = stats;
        Ok(ReleaseAction::Pages(info.span))
    }
}

// Slabs retain their class, not each object's original requested layout.
fn validate_original_layout(info: AllocationInfo, layout: Option<Layout>) -> Result<(), HeapError> {
    let Some(layout) = layout else {
        return Ok(());
    };
    let valid = match info.kind {
        AllocationKind::Slab(class) => {
            layout.size() != 0 && layout.size() <= class.size() && layout.align() <= class.size()
        }
        AllocationKind::Large => {
            Some(layout.size()) == info.requested_size && layout.align() == info.align
        }
    };
    if valid {
        Ok(())
    } else {
        Err(HeapError::LayoutMismatch)
    }
}
