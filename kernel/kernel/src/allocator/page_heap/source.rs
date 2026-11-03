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

//! Virtual page reservations backed by individually owned physical frames.
use crate::{
    mm::{
        kernel_phys_to_virt,
        kernel_space::{KernelAddressSpace, HEAP_END, HEAP_START},
        paging::{first_fit::FirstFitFrameAllocator, FrameStats},
        PhysicalAddress, KERNEL_VIRT_OFFSET,
    },
    sync::SpinLock,
};
use allocator_crate::page_heap::{Area, AreaIndex, PageRequest, PageSpan, PAGE_SIZE};
use core::{
    mem::{align_of, size_of},
    ptr::NonNull,
};

/// Owns virtually contiguous, writable spans and stable Area descriptors.
///
/// # Safety
/// Sources serialize VA reservations and retain metadata/backing until release.
/// Failed requests return all resources. Source methods run outside heap locks.
pub unsafe trait PageSource: Sync {
    fn allocate(&self, request: PageRequest) -> Option<PageSpan>;
    /// # Safety
    /// The heap has detached this allocation and all payload users have stopped.
    unsafe fn release(&self, span: PageSpan);
    fn frame_stats(&self) -> FrameStats;
    /// An optimistic capacity estimate, bounded by VA gaps and free RAM.
    fn largest_free_run_bytes(&self) -> usize;
}

#[repr(C)]
struct Mapping {
    area: Area,
    pool: usize,
}
#[repr(C)]
struct PoolPage {
    next: usize,
    prev: usize,
    occupied: u64,
}
const SLOT_OFFSET: usize =
    (size_of::<PoolPage>() + align_of::<Mapping>() - 1) & !(align_of::<Mapping>() - 1);
const SLOTS: usize = (PAGE_SIZE - SLOT_OFFSET) / size_of::<Mapping>();
const _: () = assert!(SLOTS > 0 && SLOTS <= 64);
struct VmapState {
    pool: SpinLock<usize>,
    areas: SpinLock<AreaIndex<1>>,
}

impl VmapState {
    const fn new() -> Self {
        Self {
            pool: SpinLock::new(0),
            areas: SpinLock::new(AreaIndex::new()),
        }
    }

    // The mapper must undo partial mappings before returning an error.
    fn allocate(
        &self,
        allocator: &FirstFitFrameAllocator,
        request: PageRequest,
        map: impl FnOnce(usize, usize) -> Result<(), &'static str>,
    ) -> Option<PageSpan> {
        let bytes = request.pages.checked_mul(PAGE_SIZE)?;
        if request.pages == 0 || request.align < PAGE_SIZE || !request.align.is_power_of_two() {
            return None;
        }
        let mut pending = MappingReservation::new(self, allocator, request.pages)?;
        let mapping = pending.node?.as_ptr();
        let start = {
            let mut areas = self.areas.irqsave_lock();
            let start = areas.find_gap(HEAP_START, HEAP_END, bytes, request.align)?;
            unsafe {
                (*mapping).area = Area::new(start, request.pages).unwrap();
                areas
                    .insert(NonNull::new_unchecked(core::ptr::addr_of_mut!(
                        (*mapping).area
                    )))
                    .ok()?;
            }
            pending.reserved = true;
            start
        };
        map(start, request.pages).ok()?;
        pending.mapped = true;
        pending.commit()
    }
}

static VMAP: VmapState = VmapState::new();

// No GlobalAlloc, TinyArc, Vec or heap mapping is used by this metadata pool.
fn acquire_metadata(
    state: &VmapState,
    allocator: &FirstFitFrameAllocator,
) -> Option<(*mut Mapping, usize)> {
    {
        let head = state.pool.irqsave_lock();
        let mut page = *head;
        while page != 0 {
            let header = unsafe { &mut *(page as *mut PoolPage) };
            if let Some(slot) = (0..SLOTS).find(|i| header.occupied & (1u64 << i) == 0) {
                header.occupied |= 1u64 << slot;
                return Some((
                    (page + SLOT_OFFSET + slot * size_of::<Mapping>()) as *mut Mapping,
                    page,
                ));
            }
            page = header.next;
        }
    }
    let frame = allocator.alloc_frame()?;
    let page = kernel_phys_to_virt(frame).into_raw();
    let mut head = state.pool.irqsave_lock();
    unsafe {
        (page as *mut PoolPage).write(PoolPage {
            next: *head,
            prev: 0,
            occupied: 1,
        });
        if *head != 0 {
            (*(*head as *mut PoolPage)).prev = page;
        }
    }
    *head = page;
    Some(((page + SLOT_OFFSET) as *mut Mapping, page))
}
unsafe fn release_metadata(
    state: &VmapState,
    allocator: &FirstFitFrameAllocator,
    mapping: *mut Mapping,
) {
    let page = (*mapping).pool;
    let slot = (mapping as usize - page - SLOT_OFFSET) / size_of::<Mapping>();
    let empty = {
        let mut head = state.pool.irqsave_lock();
        let h = &mut *(page as *mut PoolPage);
        assert!(slot < SLOTS && h.occupied & (1u64 << slot) != 0);
        core::ptr::drop_in_place(mapping);
        h.occupied &= !(1u64 << slot);
        if h.occupied == 0 {
            if h.prev == 0 {
                *head = h.next;
            } else {
                (*(h.prev as *mut PoolPage)).next = h.next;
            }
            if h.next != 0 {
                (*(h.next as *mut PoolPage)).prev = h.prev;
            }
            true
        } else {
            false
        }
    };
    if empty {
        allocator
            .free_frame(PhysicalAddress::new(page - KERNEL_VIRT_OFFSET))
            .expect("release mapping metadata");
    }
}

/// Own metadata, a VA reservation and its mapping until publication.
#[must_use = "unpublished virtual mappings are rolled back on drop"]
struct MappingReservation<'a> {
    state: &'a VmapState,
    allocator: &'a FirstFitFrameAllocator,
    node: Option<NonNull<Mapping>>,
    reserved: bool,
    mapped: bool,
    pages: usize,
}
impl<'a> MappingReservation<'a> {
    fn new(
        state: &'a VmapState,
        allocator: &'a FirstFitFrameAllocator,
        pages: usize,
    ) -> Option<Self> {
        let (mapping, pool) = acquire_metadata(state, allocator)?;
        // Initialize even before finding a gap, so metadata-only rollback has
        // a fully initialized value and never needs another allocation.
        unsafe {
            mapping.write(Mapping {
                area: Area::new(HEAP_START, 1).unwrap(),
                pool,
            });
        }
        Some(Self {
            state,
            allocator,
            node: NonNull::new(mapping),
            reserved: false,
            mapped: false,
            pages,
        })
    }
    fn commit(mut self) -> Option<PageSpan> {
        let mapping = self.node?;
        let area =
            unsafe { NonNull::new_unchecked(core::ptr::addr_of_mut!((*mapping.as_ptr()).area)) };
        let start = unsafe { area.as_ref().start };
        let span = unsafe {
            PageSpan::new(NonNull::new(start as *mut u8)?, self.pages)
                .ok()?
                .with_area(area)
                .ok()?
        };
        self.node = None;
        Some(span)
    }
}
impl Drop for MappingReservation<'_> {
    fn drop(&mut self) {
        let Some(node) = self.node else {
            return;
        };
        let start = unsafe { node.as_ref().area.start };
        if self.mapped {
            unsafe {
                KernelAddressSpace::get()
                    .unwrap()
                    .release_heap(start, self.pages)
            };
        }
        if self.reserved {
            assert!(self.state.areas.irqsave_lock().remove(start).is_some());
        }
        unsafe {
            release_metadata(self.state, self.allocator, node.as_ptr());
        }
    }
}

// Virtual address ownership is independent of physical frame placement.
pub struct VmapSource;
// SAFETY: reservations remain indexed until all CPUs have retired their old
// translations; both physical backing and descriptor storage are exclusively owned.
unsafe impl PageSource for VmapSource {
    fn allocate(&self, request: PageRequest) -> Option<PageSpan> {
        VMAP.allocate(
            FirstFitFrameAllocator::instance(),
            request,
            |start, pages| {
                KernelAddressSpace::get()
                    .ok_or("kernel space not initialized")?
                    .map_heap(start, pages)
            },
        )
    }

    unsafe fn release(&self, span: PageSpan) {
        let node = span.area().expect("mapped span descriptor");
        assert!(node.as_ref().detached(), "object heap still owns mapping");
        KernelAddressSpace::get()
            .expect("kernel space")
            .release_heap(span.start().as_ptr().addr(), span.pages());
        assert_eq!(
            VMAP.areas
                .irqsave_lock()
                .remove(span.start().as_ptr().addr()),
            Some(node)
        );
        release_metadata(
            &VMAP,
            FirstFitFrameAllocator::instance(),
            node.as_ptr().cast::<Mapping>(),
        );
    }
    fn frame_stats(&self) -> FrameStats {
        FirstFitFrameAllocator::instance()
            .frame_stats()
            .expect("frame allocator initialized")
    }
    fn largest_free_run_bytes(&self) -> usize {
        let virtual_bytes = VMAP.areas.irqsave_lock().largest_gap(HEAP_START, HEAP_END);
        virtual_bytes.min(self.frame_stats().free.saturating_mul(PAGE_SIZE))
    }
}

/// Exclusive, unpublished pages; dropping this handle returns them to source.
#[must_use = "uncommitted pages are returned to their source on drop"]
pub struct PendingPages<'a, P: PageSource> {
    source: &'a P,
    span: Option<PageSpan>,
}

impl<'a, P: PageSource> PendingPages<'a, P> {
    pub fn acquire(source: &'a P, request: PageRequest) -> Option<Self> {
        Some(Self {
            source,
            span: Some(source.allocate(request)?),
        })
    }

    pub fn span(&self) -> PageSpan {
        self.span.expect("pending pages already committed")
    }

    /// Transfer ownership without executing Drop, even inside the heap lock.
    pub fn commit(mut self) -> PageSpan {
        let span = self.span.take().expect("pending pages already committed");
        // Only a borrowed source remains; forgetting it leaks no resource.
        core::mem::forget(self);
        span
    }
}

impl<P: PageSource> Drop for PendingPages<'_, P> {
    fn drop(&mut self) {
        if let Some(span) = self.span.take() {
            // SAFETY: this handle exclusively owns its unpublished allocation.
            unsafe { self.source.release(span) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate as blueos;
    use crate::mm::{
        paging::{
            first_fit::{tests::Fixture, FrameState},
            mapper::PageMapper,
            PageFormat,
        },
        VirtualAddress,
    };
    use blueos_test_macro::test;
    use core::cell::Cell;

    #[test(thread = 2, repeat = 4)]
    fn failed_mapping_restores_virtual_space_frames_and_metadata() {
        // Global VA/frame snapshots can change while other CPUs allocate or
        // release memory. Exercise the real rollback path with private state
        // and a small frame budget, without exhausting the kernel's frames.
        for free in 2..crate::arch::page::PageEntry::LEVELS as usize + 4 {
            let mut states = [FrameState::Reserved; 8];
            states[..free].fill(FrameState::Free);
            let fixture = Fixture::new(states);
            let allocator = fixture.frame_allocator();
            let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
            let before = allocator.frame_stats().unwrap();
            let state = VmapState::new();
            let mapped = Cell::new(false);
            assert!(state
                .allocate(
                    allocator,
                    PageRequest {
                        pages: 3,
                        align: PAGE_SIZE,
                    },
                    |start, pages| {
                        mapped.set(true);
                        assert_eq!(start, HEAP_START);
                        unsafe {
                            mapper.map_owned_range(VirtualAddress::new(start), pages * PAGE_SIZE)
                        }
                    },
                )
                .is_none());
            assert!(mapped.get());
            assert_eq!(
                state.areas.irqsave_lock().largest_gap(HEAP_START, HEAP_END),
                HEAP_END - HEAP_START
            );
            assert_eq!(*state.pool.irqsave_lock(), 0);
            for page in 0..3 {
                assert!(mapper.translate(HEAP_START + page * PAGE_SIZE).is_none());
            }
            let after = allocator.frame_stats().unwrap();
            assert_eq!(
                (after.free, after.allocated),
                (before.free, before.allocated)
            );

            // VA exhaustion must also roll back metadata without calling the mapper.
            assert!(state
                .allocate(
                    allocator,
                    PageRequest {
                        pages: (HEAP_END - HEAP_START) / PAGE_SIZE + 1,
                        align: PAGE_SIZE,
                    },
                    |_, _| panic!("oversized reservation reached the mapper"),
                )
                .is_none());
            assert_eq!(*state.pool.irqsave_lock(), 0);
            assert_eq!(allocator.frame_stats().unwrap(), after);
        }

        let next = VmapSource
            .allocate(PageRequest {
                pages: 1,
                align: PAGE_SIZE,
            })
            .unwrap();
        unsafe { VmapSource.release(next) };
    }
}
