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

pub mod source;
#[cfg(test)]
mod tests;

use allocator_crate::page_heap::{
    classify, AllocationPlan, HeapError, HeapStats, PageHeap as RawHeap, PageRequest, PageWindow,
    ReleaseAction, SlabCommit, PAGE_SIZE,
};
use core::{alloc::Layout, ptr::NonNull};

use self::source::{PageSource, PendingPages, VmapSource};
use crate::{mm::paging::FrameStats, sync::SpinLock};

pub(super) fn memory_info_from_frames(stats: FrameStats) -> allocator_crate::MemoryInfo {
    allocator_crate::MemoryInfo {
        total: (stats.total - stats.reserved) * PAGE_SIZE,
        used: stats.allocated * PAGE_SIZE,
        max_used: stats.peak_allocated * PAGE_SIZE,
    }
}

pub struct PageHeap<P: PageSource = VmapSource> {
    state: SpinLock<Option<RawHeap>>,
    source: P,
}

impl PageHeap<VmapSource> {
    pub const fn new() -> Self {
        Self::with_source(VmapSource)
    }
}

impl<P: PageSource> PageHeap<P> {
    pub const fn with_source(source: P) -> Self {
        Self {
            state: SpinLock::new(None),
            source,
        }
    }

    /// Initialize an empty object heap over its source's virtual window.
    ///
    /// # Safety
    /// The source must retain exclusive mapped backing and stable descriptors
    /// for all committed spans until the heap detaches and returns them.
    pub unsafe fn init(&self, window: PageWindow) -> Result<(), HeapError> {
        let raw = unsafe { RawHeap::new(window) }?;
        let mut state = self.state.irqsave_lock();
        if state.is_some() {
            return Err(HeapError::Conflict);
        }
        *state = Some(raw);
        Ok(())
    }

    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        match classify(layout).ok()? {
            AllocationPlan::Slab(class) => {
                {
                    let mut guard = self.state.irqsave_lock();
                    if let Some(allocation) = guard.as_mut()?.try_alloc_small(class).ok()? {
                        return Some(allocation.ptr);
                    }
                }
                let request = PageRequest {
                    pages: 1,
                    align: PAGE_SIZE,
                };
                let Some(candidate) = PendingPages::acquire(&self.source, request) else {
                    // Another CPU may have supplied a slab while we tried the source.
                    let mut guard = self.state.irqsave_lock();
                    return guard.as_mut()?.try_alloc_small(class).ok()?.map(|a| a.ptr);
                };
                // Keep the owner outside the lock scope on every commit branch.
                let mut pending = Some(candidate);
                let span = pending.as_ref().unwrap().span();
                // SAFETY: pending exclusively owns this unpublished page.
                unsafe { RawHeap::format_slab(span, class) }.ok()?;
                let outcome = {
                    let mut guard = self.state.irqsave_lock();
                    match guard.as_mut() {
                        Some(raw) => match unsafe { raw.commit_slab(span, class) } {
                            Ok(SlabCommit::Inserted(allocation)) => {
                                let _committed = pending.take().unwrap().commit();
                                Ok(allocation.ptr)
                            }
                            Ok(SlabCommit::Existing(allocation)) => Ok(allocation.ptr),
                            Err(error) => Err(error),
                        },
                        None => Err(HeapError::InvalidGeometry),
                    }
                };
                drop(pending);
                outcome.ok()
            }
            AllocationPlan::Pages(request) => {
                let mut pending = Some(PendingPages::acquire(&self.source, request)?);
                let span = pending.as_ref().unwrap().span();
                let outcome = {
                    let mut guard = self.state.irqsave_lock();
                    match guard.as_mut() {
                        Some(raw) => match unsafe { raw.commit_large(span, layout) } {
                            Ok(allocation) => {
                                let _committed = pending.take().unwrap().commit();
                                Ok(allocation.ptr)
                            }
                            Err(error) => Err(error),
                        },
                        None => Err(HeapError::InvalidGeometry),
                    }
                };
                drop(pending);
                outcome.ok()
            }
        }
    }

    /// # Safety
    /// `ptr` must be a live allocation from this heap with its original layout;
    /// the caller must relinquish all accesses to the allocation.
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { self.free_impl(ptr, Some(layout)) };
    }

    /// # Safety
    /// `ptr` must be a live allocation from this heap and the caller must
    /// relinquish all accesses to it.
    pub unsafe fn deallocate_unknown_align(&self, ptr: *mut u8) {
        unsafe { self.free_impl(ptr, None) };
    }

    unsafe fn free_impl(&self, pointer: *mut u8, original_layout: Option<Layout>) {
        let pointer =
            NonNull::new(pointer).unwrap_or_else(|| fail_invalid_free(HeapError::NotAllocated));
        let action = {
            let mut guard = self.state.irqsave_lock();
            match guard.as_mut() {
                Some(raw) => unsafe { raw.free(pointer, original_layout) },
                None => Err(HeapError::InvalidGeometry),
            }
        };
        // Both source calls and the terminating diagnostic run after unlock.
        match action {
            Ok(ReleaseAction::None) => {}
            Ok(ReleaseAction::Pages(span)) => unsafe { self.source.release(span) },
            Err(error) => fail_invalid_free(error),
        }
    }

    pub fn malloc(&self, size: usize) -> *mut u8 {
        self.malloc_align(size, core::mem::align_of::<usize>())
    }

    pub fn malloc_align(&self, size: usize, align: usize) -> *mut u8 {
        if size == 0 {
            return core::ptr::null_mut();
        }
        let Ok(layout) = Layout::from_size_align(size, align) else {
            return core::ptr::null_mut();
        };
        self.alloc(layout)
            .map_or(core::ptr::null_mut(), NonNull::as_ptr)
    }

    pub fn calloc(&self, count: usize, size: usize) -> *mut u8 {
        let Some(bytes) = count.checked_mul(size) else {
            return core::ptr::null_mut();
        };
        let ptr = self.malloc(bytes);
        if !ptr.is_null() {
            unsafe { ptr.write_bytes(0, bytes) };
        }
        ptr
    }

    /// # Safety
    /// The pointer must be null or a live allocation from this heap.
    pub unsafe fn free(&self, ptr: *mut u8) {
        if !ptr.is_null() {
            unsafe { self.free_impl(ptr, None) };
        }
    }

    /// # Safety
    /// The pointer must be null or a live allocation from this heap, and the
    /// alignment hint must be compatible with it.
    pub unsafe fn free_align(&self, ptr: *mut u8, align: usize) {
        if let Some(ptr) = NonNull::new(ptr) {
            let valid = align.is_power_of_two() && ptr.as_ptr().addr() & (align - 1) == 0;
            if !valid {
                fail_invalid_free(HeapError::LayoutMismatch);
            }
            unsafe { self.free_impl(ptr.as_ptr(), None) };
        }
    }

    /// # Safety
    /// `ptr` must be a live allocation with the original layout and exclusively
    /// accessible by the caller. On success it is invalidated.
    pub unsafe fn realloc(&self, ptr: *mut u8, old: Layout, size: usize) -> Option<NonNull<u8>> {
        unsafe { self.realloc_impl(ptr, Some(old), size) }
    }

    /// # Safety
    /// `ptr` must be a live allocation exclusively accessible by the caller.
    pub unsafe fn realloc_unknown_align(&self, ptr: *mut u8, size: usize) -> Option<NonNull<u8>> {
        unsafe { self.realloc_impl(ptr, None, size) }
    }

    unsafe fn realloc_impl(
        &self,
        ptr: *mut u8,
        original_layout: Option<Layout>,
        size: usize,
    ) -> Option<NonNull<u8>> {
        let old_ptr = NonNull::new(ptr)?;
        let (old_info, new_layout, reused) = {
            let mut guard = self.state.irqsave_lock();
            let raw = guard.as_mut()?;
            let old_info = raw.allocation_info(old_ptr).ok()?;
            let align = original_layout.map_or(old_info.align, |layout| layout.align());
            let new_layout = Layout::from_size_align(size, align).ok()?;
            let reused = unsafe { raw.try_reuse(old_ptr, original_layout, new_layout) }.ok()?;
            (old_info, new_layout, reused)
        };
        if reused {
            return Some(old_ptr);
        }
        let new_ptr = self.alloc(new_layout)?;
        let copy_size = original_layout
            .map_or(
                old_info.requested_size.unwrap_or(old_info.capacity),
                |layout| layout.size(),
            )
            .min(size);
        unsafe { core::ptr::copy_nonoverlapping(old_ptr.as_ptr(), new_ptr.as_ptr(), copy_size) };
        unsafe { self.free_impl(old_ptr.as_ptr(), original_layout) };
        Some(new_ptr)
    }

    /// # Safety
    /// `ptr` must be null or a live allocation exclusively accessible by the caller.
    pub unsafe fn c_realloc(&self, ptr: *mut u8, size: usize) -> *mut u8 {
        if ptr.is_null() {
            return self.malloc(size);
        }
        if size == 0 {
            unsafe { self.free(ptr) };
            return core::ptr::null_mut();
        }
        unsafe { self.realloc_unknown_align(ptr, size) }
            .map_or(core::ptr::null_mut(), NonNull::as_ptr)
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> usize {
        let result = self
            .state
            .irqsave_lock()
            .as_ref()
            .and_then(|raw| raw.allocation_info(ptr).ok());
        result.map_or(0, |info| info.capacity)
    }

    pub fn memory_info(&self) -> allocator_crate::MemoryInfo {
        memory_info_from_frames(self.source.frame_stats())
    }

    /// The heap and source snapshots are taken separately and may race with allocations.
    pub fn get_max_free_block_size(&self) -> usize {
        let slot = self
            .state
            .irqsave_lock()
            .as_ref()
            .map_or(0, RawHeap::largest_free_slot);
        slot.max(self.source.largest_free_run_bytes())
    }

    pub fn heap_stats(&self) -> HeapStats {
        self.state
            .irqsave_lock()
            .as_ref()
            .map_or_else(HeapStats::default, RawHeap::stats)
    }
}

#[cold]
fn fail_invalid_free(error: HeapError) -> ! {
    // Kernel and rsrt panic handlers terminate; this never unwinds GlobalAlloc.
    panic!("invalid page heap free: {:?}", error)
}
