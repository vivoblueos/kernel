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

//! Physical frame ownership backed by a static array of per-page states.
//!
//! Paging systems use `instance()` for page tables, kernel heap backing and
//! user pages. Prefer `alloc_owned_frames` for rollback during construction and
//! `alloc_zeroed_frame` before exposing a page to users. Guards return frames
//! on drop; `into_raw` transfers ownership to a mapping's lifecycle manager.

use super::{FrameAllocator, FrameDeallocationError, FrameStats, FrameUsage};
use crate::{
    mm::{kernel_phys_to_virt, memory_bank::MemoryRegion, paging::PageFormat, PhysicalAddress},
    sync::SpinLock,
};
use core::ptr::addr_of_mut;

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

const PHYS_BASE: usize = crate::boards::PHYS_DRAM_BASE as usize;
const PAGE_SIZE: usize = <crate::arch::page::PageEntry as PageFormat>::PAGE_SIZE;
const FRAME_COUNT: usize = crate::boards::PHYS_DRAM_SIZE as usize / PAGE_SIZE;
static mut STATES: [FrameState; FRAME_COUNT] = [FrameState::Free; FRAME_COUNT];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum FrameState {
    Free,
    Reserved,
    Allocated,
}

struct AllocatorState {
    base: usize,
    page_size: usize,
    states: &'static mut [FrameState],
    // No free frame exists below this index. Freeing updates the cursor.
    first_free: usize,
    reserved: usize,
    allocated: usize,
    free: usize,
    peak_allocated: usize,
}

/// The system's shared allocator is accessed through [`Self::instance`].
///
/// The caller supplies a static state array at initialization. Pages containing
/// the kernel, metadata, or other live objects must not be marked free.
/// Independently constructed allocators must own disjoint backing memory.
pub struct FirstFitFrameAllocator {
    state: SpinLock<Option<AllocatorState>>,
}

static FIRST_FIT: FirstFitFrameAllocator = FirstFitFrameAllocator::new();

impl FirstFitFrameAllocator {
    pub const fn new() -> Self {
        Self {
            state: SpinLock::new(None),
        }
    }

    pub fn instance() -> &'static Self {
        &FIRST_FIT
    }

    /// Initialize this allocator for `[base, base + N * page_size)`.
    ///
    /// Returns `None` if already initialized, the page size is not a nonzero
    /// power of two, the base is misaligned, or the physical range overflows.
    ///
    /// # Safety
    /// Free pages must be valid RAM exclusively owned by this allocator and
    /// must not overlap any live objects, including the allocator itself.
    /// Every free page must be writable through the kernel direct map. The RAM
    /// must remain valid for the lifetime of all returned frames.
    pub unsafe fn init(&self, regions: &[MemoryRegion]) -> Option<()> {
        let states = &mut *addr_of_mut!(STATES);
        let page_size = PAGE_SIZE;
        let base = PHYS_BASE;

        if !page_size.is_power_of_two() || base & (page_size - 1) != 0 {
            return None;
        }
        let size = states.len().checked_mul(page_size)?;
        let end = base.checked_add(size)?;
        states.fill(FrameState::Reserved);
        // init framestate array
        for region in regions.iter().filter(|r| !r.is_reserved) {
            let start = region.base.into_raw();
            let region_end = start.checked_add(region.size)?;
            let start = start.max(base);
            let region_end = region_end.min(end);
            if start >= region_end {
                continue;
            }
            let first = (start - base).div_ceil(page_size);
            let last = (region_end - base) / page_size;
            if first < last {
                states[first..last].fill(FrameState::Free);
            }
        }

        let mut state = self.state.irqsave_lock();
        if state.is_some() {
            return None;
        }
        let free = states
            .iter()
            .filter(|state| **state == FrameState::Free)
            .count();
        let first_free = states
            .iter()
            .position(|state| *state == FrameState::Free)
            .unwrap_or(states.len());
        let reserved = states
            .iter()
            .filter(|state| **state == FrameState::Reserved)
            .count();
        let allocated = states.len() - reserved - free;
        *state = Some(AllocatorState {
            base,
            page_size,
            states,
            first_free,
            reserved,
            allocated,
            free,
            peak_allocated: allocated,
        });
        Some(())
    }

    pub fn usage(&self) -> Option<FrameUsage> {
        let state = self.state.irqsave_lock();
        let state = state.as_ref()?;
        Some(FrameUsage::new(
            state.states.len() - state.free,
            state.states.len(),
        ))
    }

    /// Snapshot the physical frame counts under the allocator lock.
    pub fn frame_stats(&self) -> Option<FrameStats> {
        let state = self.state.irqsave_lock();
        let state = state.as_ref()?;
        Some(FrameStats {
            total: state.states.len(),
            reserved: state.reserved,
            allocated: state.allocated,
            free: state.free,
            peak_allocated: state.peak_allocated,
        })
    }

    /// Return the longest contiguous free run, in pages.
    pub fn largest_free_run(&self) -> Option<usize> {
        let state = self.state.irqsave_lock();
        let state = state.as_ref()?;
        let mut largest = 0;
        let mut run = 0;
        for frame in &state.states[state.first_free..] {
            if *frame == FrameState::Free {
                run += 1;
                largest = largest.max(run);
            } else {
                run = 0;
            }
        }
        Some(largest)
    }

    /// Allocate one frame without clearing its previous contents.
    pub fn alloc_frame(&self) -> Option<PhysicalAddress> {
        self.alloc_frames(1)
    }

    /// Allocate a contiguous run atomically, leaving state unchanged on failure.
    /// The returned pages are owned by the caller until `free_frames`.
    pub fn alloc_frames(&self, count: usize) -> Option<PhysicalAddress> {
        self.alloc_frames_aligned(count, 1)
    }

    /// Allocate contiguous pages aligned to an absolute physical address.
    /// `align_pages` must be a nonzero power of two. Invalid requests and
    /// searches without a suitable run leave all allocator state unchanged.
    pub fn alloc_frames_aligned(
        &self,
        count: usize,
        align_pages: usize,
    ) -> Option<PhysicalAddress> {
        let mut state = self.state.irqsave_lock();
        let state = state.as_mut()?;
        if count == 0 || count > state.free || !align_pages.is_power_of_two() {
            return None;
        }
        count.checked_mul(state.page_size)?;
        let align_bytes = align_pages.checked_mul(state.page_size)?;
        let mut run = 0;
        let mut found = None;
        for index in state.first_free..state.states.len() {
            if state.states[index] == FrameState::Free {
                run += 1;
                if run >= count {
                    let first = index + 1 - count;
                    let start_addr = state
                        .base
                        .checked_add(first.checked_mul(state.page_size)?)?;
                    if start_addr & (align_bytes - 1) != 0 {
                        continue;
                    }
                    found = Some((first, start_addr));
                    break;
                }
            } else {
                run = 0;
            }
        }
        let (first, start_addr) = found?;
        state.states[first..first + count].fill(FrameState::Allocated);
        state.allocated += count;
        state.free -= count;
        state.peak_allocated = state.peak_allocated.max(state.allocated);
        // A fragmented run may have been skipped; preserve its free pages.
        if first == state.first_free {
            let end = first + count;
            state.first_free = state.states[end..]
                .iter()
                .position(|frame| *frame == FrameState::Free)
                .map_or(state.states.len(), |offset| end + offset);
        }
        Some(PhysicalAddress::new(start_addr))
    }

    /// # Safety
    /// `frame` must be exclusively owned by the caller, no longer mapped or in
    /// use by any CPU/device, and returned by this allocator.
    pub unsafe fn free_frame(&self, frame: PhysicalAddress) -> Result<(), FrameDeallocationError> {
        unsafe { self.free_frames(frame, 1) }
    }

    /// Release a contiguous allocation, validating the entire range first.
    /// Errors leave every frame unchanged. Checks diagnose invalid addresses,
    /// reserved frames and duplicate frees; they cannot establish ownership.
    ///
    /// # Safety
    /// The caller must own all `count` pages and ensure no references, active
    /// mappings, or device accesses remain. Do not release pages still owned by
    /// a `FrameAllocation`.
    pub unsafe fn free_frames(
        &self,
        frame: PhysicalAddress,
        count: usize,
    ) -> Result<(), FrameDeallocationError> {
        let mut state = self.state.irqsave_lock();
        let state = state
            .as_mut()
            .ok_or(FrameDeallocationError::NotInitialized)?;
        let offset = frame
            .into_raw()
            .checked_sub(state.base)
            .filter(|offset| offset & (state.page_size - 1) == 0)
            .ok_or(FrameDeallocationError::InvalidRange)?;
        let first = offset / state.page_size;
        let end = first
            .checked_add(count)
            .filter(|end| count != 0 && *end <= state.states.len())
            .ok_or(FrameDeallocationError::InvalidRange)?;
        for frame in &state.states[first..end] {
            match frame {
                FrameState::Reserved => return Err(FrameDeallocationError::Reserved),
                FrameState::Free => return Err(FrameDeallocationError::NotAllocated),
                FrameState::Allocated => {}
            }
        }
        state.states[first..end].fill(FrameState::Free);
        state.allocated -= count;
        state.free += count;
        state.first_free = state.first_free.min(first);
        Ok(())
    }

    /// Allocate an owned run which is automatically released on failure paths.
    pub fn alloc_owned_frames(&self, count: usize) -> Option<FrameAllocation<'_>> {
        self.alloc_owned_frames_aligned(count, 1)
    }

    /// Allocate an aligned run with automatic rollback until ownership transfer.
    pub fn alloc_owned_frames_aligned(
        &self,
        count: usize,
        align_pages: usize,
    ) -> Option<FrameAllocation<'_>> {
        Some(FrameAllocation {
            allocator: self,
            start: self.alloc_frames_aligned(count, align_pages)?,
            count,
        })
    }

    /// Allocate a cleared page suitable for exposing to a user address space.
    /// Clearing finishes before ownership is returned to the caller.
    pub fn alloc_zeroed_frame(&self) -> Option<FrameAllocation<'_>> {
        let frame = self.alloc_owned_frames(1)?;
        let page_size = self.state.irqsave_lock().as_ref()?.page_size;
        let ptr = kernel_phys_to_virt(frame.start).into_raw() as *mut u8;
        // SAFETY: init guarantees writable direct-map backing; frame owns it.
        unsafe { ptr.write_bytes(0, page_size) };
        Some(frame)
    }
}

impl Default for FirstFitFrameAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Exclusive ownership of a contiguous run of physical frames.
/// Drop releases the run; transfer ownership explicitly with `into_raw` when
/// publishing it in a mapping. Hardware users must be stopped before drop.
#[must_use = "dropping the allocation immediately releases its physical frames"]
pub struct FrameAllocation<'a> {
    allocator: &'a FirstFitFrameAllocator,
    start: PhysicalAddress,
    count: usize,
}

impl FrameAllocation<'_> {
    pub fn address(&self) -> PhysicalAddress {
        self.start
    }

    pub fn count(&self) -> usize {
        self.count
    }

    /// Transfer responsibility for releasing the frames to the caller.
    pub fn into_raw(self) -> PhysicalAddress {
        let start = self.start;
        core::mem::forget(self);
        start
    }
}

impl Drop for FrameAllocation<'_> {
    fn drop(&mut self) {
        // SAFETY: this guard owns the run until drop or into_raw.
        unsafe { self.allocator.free_frames(self.start, self.count) }
            .expect("invalid owned frame allocation");
    }
}

// SAFETY: All references access the same state under an IRQ-saving lock. Init
// requires exclusive ownership of free pages and succeeds only once. Allocated
// pages are marked before returning, so concurrent calls cannot overlap.
unsafe impl FrameAllocator for &FirstFitFrameAllocator {
    fn alloc_frame(&mut self) -> Option<PhysicalAddress> {
        FirstFitFrameAllocator::alloc_frame(self)
    }

    fn free_frame(&mut self, frame: PhysicalAddress) -> Result<(), FrameDeallocationError> {
        unsafe { FirstFitFrameAllocator::free_frame(self, frame) }
    }

    fn usage(&self) -> FrameUsage {
        FirstFitFrameAllocator::usage(self).expect("FirstFitFrameAllocator didn't be initialized.")
    }
}
