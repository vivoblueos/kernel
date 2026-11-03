// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::{mem::size_of, ptr};

const END: usize = usize::MAX;

#[repr(C)]
struct SlabHeader {
    free_head: usize,
    prev: usize,
    next: usize,
    free_count: usize,
    slot_count: usize,
    class: usize,
    occupied: [u64; 8],
}

fn geometry(class: ClassId) -> Result<(usize, usize), HeapError> {
    let size = class.size();
    let offset = size_of::<SlabHeader>()
        .checked_add(size - 1)
        .ok_or(HeapError::InvalidGeometry)?
        & !(size - 1);
    let slots = PAGE_SIZE
        .checked_sub(offset)
        .ok_or(HeapError::InvalidGeometry)?
        / size;
    if slots == 0 || slots > 512 {
        return Err(HeapError::InvalidGeometry);
    }
    Ok((offset, slots))
}

fn header(span: PageSpan) -> *mut SlabHeader {
    span.start.as_ptr().cast()
}
fn slot(span: PageSpan, offset: usize, size: usize, index: usize) -> *mut u8 {
    span.start.as_ptr().wrapping_add(offset + size * index)
}

impl PageHeap {
    /// Formats one exclusively owned page outside the heap lock.
    ///
    /// # Safety
    /// The page must be writable and exclusively owned until committed or released.
    pub unsafe fn format_slab(span: PageSpan, class: ClassId) -> Result<(), HeapError> {
        if span.pages != 1 {
            return Err(HeapError::InvalidRequest);
        }
        let (offset, slots) = geometry(class)?;
        ptr::write(
            header(span),
            SlabHeader {
                free_head: 0,
                prev: END,
                next: END,
                free_count: slots,
                slot_count: slots,
                class: class.0 as usize,
                occupied: [0; 8],
            },
        );
        for i in 0..slots {
            ptr::write(
                slot(span, offset, class.size(), i).cast::<usize>(),
                if i + 1 == slots { END } else { i + 1 },
            );
        }
        Ok(())
    }

    fn checked_header(
        &self,
        index: usize,
        class: ClassId,
    ) -> Result<(PageSpan, *mut SlabHeader), HeapError> {
        let address = self.window.span(index, 1)?.start().as_ptr().addr();
        let node = self.areas.find(address).ok_or(HeapError::CorruptMetadata)?;
        let area = unsafe { node.as_ref() };
        if area.start != address
            || area.end != address + PAGE_SIZE
            || !matches!(unsafe { area.kind() }, Kind::Slab(c) if c == class)
        {
            return Err(HeapError::CorruptMetadata);
        }
        let span = unsafe { Area::span(node) };
        let h = header(span);
        let (_, slots) = geometry(class)?;
        unsafe {
            let v = &*h;
            let count: usize = v.occupied.iter().map(|x| x.count_ones() as usize).sum();
            if v.class != class.0 as usize
                || v.slot_count != slots
                || v.free_count > slots
                || count != slots - v.free_count
                || (v.free_count == 0) != (v.free_head == END)
                || (v.free_head != END && v.free_head >= slots)
            {
                return Err(HeapError::CorruptMetadata);
            }
        }
        Ok((span, h))
    }

    fn links(&self, index: usize, class: ClassId, h: *mut SlabHeader) -> Result<(), HeapError> {
        unsafe {
            let (prev, next) = ((*h).prev, (*h).next);
            if prev == END {
                if self.partial[class.0 as usize] != index {
                    return Err(HeapError::CorruptMetadata);
                }
            } else if (*self.checked_header(prev, class)?.1).next != index {
                return Err(HeapError::CorruptMetadata);
            }
            if next != END && (*self.checked_header(next, class)?.1).prev != index {
                return Err(HeapError::CorruptMetadata);
            }
        }
        Ok(())
    }

    unsafe fn unlink(&mut self, class: ClassId, h: *mut SlabHeader) {
        let (prev, next) = ((*h).prev, (*h).next);
        if prev == END {
            self.partial[class.0 as usize] = next;
        } else {
            (*header(self.window.span(prev, 1).unwrap())).next = next;
        }
        if next != END {
            (*header(self.window.span(next, 1).unwrap())).prev = prev;
        }
        (*h).prev = END;
        (*h).next = END;
    }

    unsafe fn link(&mut self, index: usize, class: ClassId, h: *mut SlabHeader) {
        let next = self.partial[class.0 as usize];
        (*h).prev = END;
        (*h).next = next;
        if next != END {
            (*header(self.window.span(next, 1).unwrap())).prev = index;
        }
        self.partial[class.0 as usize] = index;
    }

    pub fn try_alloc_small(&mut self, class: ClassId) -> Result<Option<Allocation>, HeapError> {
        let index = self.partial[class.0 as usize];
        if index == END {
            return Ok(None);
        }
        let (span, h) = self.checked_header(index, class)?;
        self.links(index, class, h)?;
        let (offset, _) = geometry(class)?;
        unsafe {
            let i = (*h).free_head;
            if i == END || ((*h).occupied[i / 64] & (1u64 << (i % 64))) != 0 {
                return Err(HeapError::CorruptMetadata);
            }
            let p = slot(span, offset, class.size(), i);
            let next = ptr::read(p.cast::<usize>());
            if (next != END && next >= (*h).slot_count) || ((*h).free_count == 1) != (next == END) {
                return Err(HeapError::CorruptMetadata);
            }
            let mut stats = self.stats;
            stats.live_objects = stats
                .live_objects
                .checked_add(1)
                .ok_or(HeapError::InvalidRequest)?;
            stats.charged_bytes = stats
                .charged_bytes
                .checked_add(class.size())
                .ok_or(HeapError::InvalidRequest)?;
            stats.peak_charged_bytes = stats.peak_charged_bytes.max(stats.charged_bytes);
            (*h).free_head = next;
            (*h).free_count -= 1;
            (*h).occupied[i / 64] |= 1u64 << (i % 64);
            if (*h).free_count == 0 {
                self.unlink(class, h);
            }
            self.stats = stats;
            Ok(Some(Allocation {
                ptr: NonNull::new_unchecked(p),
                capacity: class.size(),
            }))
        }
    }

    /// Publishes a formatted candidate only if existing slabs have no capacity.
    ///
    /// # Safety
    /// The candidate must be an exclusively owned, writable page formatted for
    /// this class; after insertion its ownership remains with the heap.
    pub unsafe fn commit_slab(
        &mut self,
        span: PageSpan,
        class: ClassId,
    ) -> Result<SlabCommit, HeapError> {
        if let Some(a) = self.try_alloc_small(class)? {
            return Ok(SlabCommit::Existing(a));
        }
        if span.pages != 1 {
            return Err(HeapError::InvalidRequest);
        }
        let index = self.window.index_of(span.start)?;
        let area = self.candidate(span)?;
        let (_, slots) = geometry(class)?;
        let h = header(span);
        if (*h).class != class.0 as usize
            || (*h).slot_count != slots
            || (*h).free_count != slots
            || (*h).free_head != 0
            || (*h).prev != END
            || (*h).next != END
            || (*h).occupied != [0; 8]
        {
            return Err(HeapError::CorruptMetadata);
        }
        for i in 0..slots {
            let expected = if i + 1 == slots { END } else { i + 1 };
            if ptr::read(slot(span, geometry(class)?.0, class.size(), i).cast::<usize>())
                != expected
            {
                return Err(HeapError::CorruptMetadata);
            }
        }
        let mut stats = self.stats;
        stats.slab_pages = stats
            .slab_pages
            .checked_add(1)
            .ok_or(HeapError::InvalidRequest)?;
        stats.backing_bytes = stats
            .backing_bytes
            .checked_add(PAGE_SIZE)
            .ok_or(HeapError::InvalidRequest)?;
        stats.live_objects = stats
            .live_objects
            .checked_add(1)
            .ok_or(HeapError::InvalidRequest)?;
        stats.charged_bytes = stats
            .charged_bytes
            .checked_add(class.size())
            .ok_or(HeapError::InvalidRequest)?;
        stats.peak_charged_bytes = stats.peak_charged_bytes.max(stats.charged_bytes);
        let p = slot(span, geometry(class)?.0, class.size(), 0);
        (*h).free_head = if slots == 1 { END } else { 1 };
        (*h).free_count -= 1;
        (*h).occupied[0] = 1;
        self.areas.insert(area)?;
        area.as_ref().set_kind(Kind::Slab(class));
        if slots > 1 {
            self.link(index, class, h);
        }
        self.stats = stats;
        Ok(SlabCommit::Inserted(Allocation {
            ptr: NonNull::new_unchecked(p),
            capacity: class.size(),
        }))
    }

    pub(super) fn slab_info(
        &self,
        index: usize,
        ptr: NonNull<u8>,
        class: ClassId,
    ) -> Result<AllocationInfo, HeapError> {
        let (span, h) = self.checked_header(index, class)?;
        let (offset, slots) = geometry(class)?;
        let rel = ptr.as_ptr().addr() - span.start.as_ptr().addr();
        if rel < offset
            || rel >= offset + slots * class.size()
            || (rel - offset) & (class.size() - 1) != 0
        {
            return Err(HeapError::InteriorPointer);
        }
        let i = (rel - offset) / class.size();
        if unsafe { (*h).occupied[i / 64] & (1u64 << (i % 64)) == 0 } {
            return Err(HeapError::NotAllocated);
        }
        Ok(AllocationInfo {
            kind: AllocationKind::Slab(class),
            requested_size: None,
            capacity: class.size(),
            align: class.size(),
            span,
        })
    }

    pub(super) unsafe fn free_slab(
        &mut self,
        ptr: NonNull<u8>,
        info: AllocationInfo,
    ) -> Result<ReleaseAction, HeapError> {
        let AllocationKind::Slab(class) = info.kind else {
            return Err(HeapError::CorruptMetadata);
        };
        let index = self.window.index_of(ptr)?;
        let (span, h) = self.checked_header(index, class)?;
        let (offset, _) = geometry(class)?;
        let i = (ptr.as_ptr().addr() - span.start.as_ptr().addr() - offset) / class.size();
        let was_full = (*h).free_count == 0;
        let empty = (*h).free_count + 1 == (*h).slot_count;
        if !was_full {
            self.links(index, class, h)?;
        }
        if was_full && !empty {
            let next = self.partial[class.0 as usize];
            if next != END {
                let (_, n) = self.checked_header(next, class)?;
                self.links(next, class, n)?;
            }
        }
        let mut stats = self.stats;
        stats.live_objects = stats
            .live_objects
            .checked_sub(1)
            .ok_or(HeapError::CorruptMetadata)?;
        stats.charged_bytes = stats
            .charged_bytes
            .checked_sub(class.size())
            .ok_or(HeapError::CorruptMetadata)?;
        if empty {
            stats.slab_pages = stats
                .slab_pages
                .checked_sub(1)
                .ok_or(HeapError::CorruptMetadata)?;
            stats.backing_bytes = stats
                .backing_bytes
                .checked_sub(PAGE_SIZE)
                .ok_or(HeapError::CorruptMetadata)?;
        }
        (*h).occupied[i / 64] &= !(1u64 << (i % 64));
        ptr::write(ptr.as_ptr().cast::<usize>(), (*h).free_head);
        (*h).free_head = i;
        (*h).free_count += 1;
        if empty {
            if !was_full {
                self.unlink(class, h);
            }
            let node = self
                .areas
                .remove(span.start().as_ptr().addr())
                .ok_or(HeapError::CorruptMetadata)?;
            node.as_ref().set_kind(Kind::Empty);
        } else if was_full {
            self.link(index, class, h);
        }
        self.stats = stats;
        Ok(if empty {
            ReleaseAction::Pages(span)
        } else {
            ReleaseAction::None
        })
    }
}
