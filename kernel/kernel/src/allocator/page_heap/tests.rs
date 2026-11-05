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

use super::{
    memory_info_from_frames,
    source::{PageSource, PendingPages, VmapSource},
    PageHeap,
};
use crate::{mm::paging::FrameStats, sync::SpinLock};
use alloc::sync::{Arc, Weak};
use allocator_crate::page_heap::{PageRequest, PageSpan, PageWindow, PAGE_SIZE};
use blueos_test_macro::test;
use core::{
    alloc::Layout,
    ptr::NonNull,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};

struct CountingSource {
    inner: VmapSource,
    fail_next: AtomicBool,
    two_page_slab_next: AtomicBool,
    #[cfg(smp)]
    race_enabled: AtomicBool,
    #[cfg(smp)]
    arrived: AtomicUsize,
    free_run_override: AtomicUsize,
    live_pages: AtomicUsize,
    probe: SpinLock<Option<Weak<PageHeap<CountingSource>>>>,
}
impl CountingSource {
    fn new() -> Self {
        Self {
            inner: VmapSource,
            fail_next: AtomicBool::new(false),
            two_page_slab_next: AtomicBool::new(false),
            #[cfg(smp)]
            race_enabled: AtomicBool::new(false),
            #[cfg(smp)]
            arrived: AtomicUsize::new(0),
            free_run_override: AtomicUsize::new(usize::MAX),
            live_pages: AtomicUsize::new(0),
            probe: SpinLock::new(None),
        }
    }
    fn assert_unlocked(&self) {
        let heap = self.probe.irqsave_lock().as_ref().and_then(Weak::upgrade);
        if let Some(heap) = heap {
            let guard = heap
                .state
                .try_lock()
                .expect("PageSource called under heap lock");
            drop(guard);
        }
    }
}
// SAFETY: forwards exclusive, mapped spans to/from the real frame source.
// The explicit fault mode violates only the single-page size requirement to
// exercise rejection of a malformed candidate; both pages remain owned.
unsafe impl PageSource for CountingSource {
    fn allocate(&self, mut request: PageRequest) -> Option<PageSpan> {
        self.assert_unlocked();
        if self.fail_next.swap(false, Ordering::AcqRel) {
            return None;
        }
        if self.two_page_slab_next.swap(false, Ordering::AcqRel) {
            assert_eq!(request.pages, 1);
            request.pages = 2;
        }
        let span = self.inner.allocate(request)?;
        self.live_pages.fetch_add(span.pages(), Ordering::AcqRel);
        #[cfg(smp)]
        if self.race_enabled.load(Ordering::Acquire) {
            self.arrived.fetch_add(1, Ordering::AcqRel);
            wait_until(|| self.arrived.load(Ordering::Acquire) >= 2);
        }
        Some(span)
    }
    unsafe fn release(&self, span: PageSpan) {
        self.assert_unlocked();
        unsafe {
            self.inner.release(span);
        }
        self.live_pages.fetch_sub(span.pages(), Ordering::AcqRel);
    }
    fn frame_stats(&self) -> FrameStats {
        self.assert_unlocked();
        self.inner.frame_stats()
    }
    fn largest_free_run_bytes(&self) -> usize {
        self.assert_unlocked();
        let value = self.free_run_override.load(Ordering::Acquire);
        if value == usize::MAX {
            self.inner.largest_free_run_bytes()
        } else {
            value
        }
    }
}

#[must_use]
struct KernelFixture {
    heap: Arc<PageHeap<CountingSource>>,
}
impl KernelFixture {
    fn new() -> Self {
        let base = crate::mm::kernel_space::HEAP_START;
        let pages = (crate::mm::kernel_space::HEAP_END - base) / PAGE_SIZE;
        let window =
            unsafe { PageWindow::new(NonNull::new(base as *mut u8).unwrap(), pages) }.unwrap();
        let heap = Arc::new(PageHeap::with_source(CountingSource::new()));
        *heap.source.probe.irqsave_lock() = Some(Arc::downgrade(&heap));
        unsafe {
            heap.init(window).unwrap();
        }
        Self { heap }
    }
}
impl Drop for KernelFixture {
    fn drop(&mut self) {
        assert_eq!(Arc::strong_count(&self.heap), 1);
        assert_eq!(self.heap.source.live_pages.load(Ordering::Acquire), 0);
    }
}

#[cfg(smp)]
fn wait_until(mut ready: impl FnMut() -> bool) {
    let deadline = crate::time::Tick::after(crate::time::Tick::from_millis(5000));
    while !ready() {
        assert!(!deadline.is_elapsed(), "page heap worker timed out");
        crate::scheduler::yield_me();
    }
}

// Catches omitted second checks and leaked redundant candidates. Both workers
// own real candidate pages before either is allowed to publish its slab.
#[cfg(smp)]
#[test]
fn concurrent_refill_returns_redundant_candidate_while_objects_are_live() {
    let f = KernelFixture::new();
    // A try_lock probe cannot distinguish this caller from another CPU's lock.
    *f.heap.source.probe.irqsave_lock() = None;
    f.heap.source.race_enabled.store(true, Ordering::Release);
    let addresses = Arc::new([AtomicUsize::new(0), AtomicUsize::new(0)]);
    let release = Arc::new(AtomicBool::new(false));
    let completed = Arc::new(AtomicUsize::new(0));
    for worker in 0..2 {
        let heap = f.heap.clone();
        let addresses = addresses.clone();
        let release = release.clone();
        let completed = completed.clone();
        crate::thread::spawn(move || {
            let layout = Layout::from_size_align(64, 8).unwrap();
            let object = heap.alloc(layout).unwrap();
            unsafe { object.as_ptr().write_bytes(0x31 + worker as u8, 64) };
            addresses[worker].store(object.as_ptr().addr(), Ordering::Release);
            wait_until(|| release.load(Ordering::Acquire));
            for offset in 0..64 {
                assert_eq!(
                    unsafe { object.as_ptr().add(offset).read() },
                    0x31 + worker as u8
                );
            }
            unsafe { heap.dealloc(object.as_ptr(), layout) };
            // Completion must not race fixture teardown or its Arc assertion.
            drop(heap);
            completed.fetch_add(1, Ordering::Release);
        })
        .expect("spawn page heap refill worker");
    }
    wait_until(|| {
        addresses
            .iter()
            .all(|address| address.load(Ordering::Acquire) != 0)
    });
    assert_ne!(
        addresses[0].load(Ordering::Acquire),
        addresses[1].load(Ordering::Acquire)
    );
    assert_eq!(f.heap.source.arrived.load(Ordering::Acquire), 2);
    let stats = f.heap.heap_stats();
    assert_eq!(stats.live_objects, 2);
    assert_eq!(stats.slab_pages, 1);
    assert_eq!(stats.backing_bytes, PAGE_SIZE);
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 1);
    release.store(true, Ordering::Release);
    wait_until(|| completed.load(Ordering::Acquire) == 2);
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
    assert_eq!(f.heap.heap_stats().live_objects, 0);
}

// Catches retaining the old 16 MiB cap and failing to return/reuse large runs.
#[test]
fn private_heap_grows_past_old_fixed_capacity_and_returns_all_pages() {
    let f = KernelFixture::new();
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
    let layout = Layout::from_size_align(20 * 1024 * 1024, PAGE_SIZE).unwrap();
    for _ in 0..3 {
        let buffer = f.heap.alloc(layout).unwrap();
        unsafe {
            buffer.as_ptr().write(0x11);
            buffer.as_ptr().add(layout.size() - 1).write(0x22);
        }
        assert_eq!(unsafe { buffer.as_ptr().read() }, 0x11);
        assert_eq!(
            unsafe { buffer.as_ptr().add(layout.size() - 1).read() },
            0x22
        );
        assert!(f.heap.heap_stats().backing_bytes > 16 * 1024 * 1024);
        assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 5120);
        unsafe { f.heap.dealloc(buffer.as_ptr(), layout) };
        assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
        assert_eq!(f.heap.heap_stats().backing_bytes, 0);
    }
}

// Heap alignment is virtual; each backing page is translated independently.
#[test]
fn private_heap_allocations_are_virtually_contiguous() {
    use crate::mm::{kernel_virt_to_phys, VirtualAddress};
    let f = KernelFixture::new();
    for size in [1025, 4096, 4097, 65537] {
        for align in [8, 4096, 65536] {
            let layout = Layout::from_size_align(size, align).unwrap();
            let buffer = f.heap.alloc(layout).unwrap();
            let start = buffer.as_ptr().addr();
            assert!(
                (crate::mm::kernel_space::HEAP_START..crate::mm::kernel_space::HEAP_END)
                    .contains(&start)
            );
            assert_eq!(start % align, 0);
            for offset in (0..size).step_by(PAGE_SIZE) {
                let physical = kernel_virt_to_phys(VirtualAddress::new(start + offset)).into_raw();
                assert_eq!(physical % PAGE_SIZE, 0);
                unsafe { buffer.as_ptr().add(offset).write(0xa5) };
            }
            for offset in (0..size).step_by(PAGE_SIZE) {
                assert_eq!(unsafe { buffer.as_ptr().add(offset).read() }, 0xa5);
            }
            unsafe { f.heap.dealloc(buffer.as_ptr(), layout) };
            assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
        }
    }
}

// Catches OOM or candidate rejection changing live objects, their owner entries,
// or accounting; malformed candidates must return both real backing pages.
#[test]
fn failed_refills_and_publication_preserve_existing_objects() {
    let f = KernelFixture::new();
    let small_layout = Layout::from_size_align(64, 8).unwrap();
    let large_layout = Layout::from_size_align(4097, 4096).unwrap();
    let small = f.heap.alloc(small_layout).unwrap();
    let large = f.heap.alloc(large_layout).unwrap();
    unsafe {
        small.as_ptr().write_bytes(0x53, small_layout.size());
        large.as_ptr().write_bytes(0xa7, large_layout.size());
    }
    let stats = f.heap.heap_stats();
    let snapshot = |info: allocator_crate::page_heap::AllocationInfo| {
        (
            info.kind,
            info.requested_size,
            info.capacity,
            info.align,
            info.span,
        )
    };
    let (small_info, large_info) = {
        let guard = f.heap.state.irqsave_lock();
        let raw = guard.as_ref().unwrap();
        (
            snapshot(raw.allocation_info(small).unwrap()),
            snapshot(raw.allocation_info(large).unwrap()),
        )
    };
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 3);
    for fault in 0..3 {
        let request = match fault {
            0 => {
                f.heap.source.fail_next.store(true, Ordering::Release);
                Layout::from_size_align(128, 8).unwrap()
            }
            1 => {
                f.heap.source.fail_next.store(true, Ordering::Release);
                Layout::from_size_align(65537, 65536).unwrap()
            }
            _ => {
                f.heap
                    .source
                    .two_page_slab_next
                    .store(true, Ordering::Release);
                Layout::from_size_align(128, 8).unwrap()
            }
        };
        assert!(f.heap.alloc(request).is_none());
        assert!(!f.heap.source.fail_next.load(Ordering::Acquire));
        assert!(!f.heap.source.two_page_slab_next.load(Ordering::Acquire));
        assert_eq!(f.heap.heap_stats(), stats);
        assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 3);
        {
            let guard = f.heap.state.irqsave_lock();
            let raw = guard.as_ref().unwrap();
            assert_eq!(snapshot(raw.allocation_info(small).unwrap()), small_info);
            assert_eq!(snapshot(raw.allocation_info(large).unwrap()), large_info);
        }
        for offset in 0..small_layout.size() {
            assert_eq!(unsafe { small.as_ptr().add(offset).read() }, 0x53);
        }
        for offset in 0..large_layout.size() {
            assert_eq!(unsafe { large.as_ptr().add(offset).read() }, 0xa7);
        }
    }
    // A successful retry proves failure did not poison publication or ownership.
    let retry_layout = Layout::from_size_align(128, 8).unwrap();
    let retry = f.heap.alloc(retry_layout).unwrap();
    unsafe {
        f.heap.dealloc(retry.as_ptr(), retry_layout);
        f.heap.dealloc(small.as_ptr(), small_layout);
        f.heap.dealloc(large.as_ptr(), large_layout);
    }
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
}

// Catches leaked OOM candidates, missing final-page return, wrong alignment,
// and taking the physical source lock while holding the heap lock.
#[test]
fn private_heap_rolls_back_oom_and_returns_pages_outside_lock() {
    let f = KernelFixture::new();
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
    f.heap.source.fail_next.store(true, Ordering::Release);
    assert!(f
        .heap
        .alloc(Layout::from_size_align(24, 8).unwrap())
        .is_none());
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
    let small = f
        .heap
        .alloc(Layout::from_size_align(24, 8).unwrap())
        .unwrap();
    let large = f
        .heap
        .alloc(Layout::from_size_align(8193, 65536).unwrap())
        .unwrap();
    assert_eq!(large.as_ptr().addr() & (65536 - 1), 0);
    unsafe {
        f.heap.deallocate_unknown_align(small.as_ptr());
        f.heap.deallocate_unknown_align(large.as_ptr());
    }
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
}

// Catches premature page release on commit and missing rollback on drop.
#[test]
fn pending_pages_roll_back_or_transfer_ownership() {
    let f = KernelFixture::new();
    let request = PageRequest {
        pages: 1,
        align: PAGE_SIZE,
    };
    let pending = PendingPages::acquire(&f.heap.source, request).unwrap();
    assert_eq!(pending.span().pages(), 1);
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 1);
    drop(pending);
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
    let pending = PendingPages::acquire(&f.heap.source, request).unwrap();
    let span = {
        let _guard = f.heap.state.irqsave_lock();
        pending.commit()
    };
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 1);
    unsafe {
        f.heap.source.release(span);
    }
}

// Catches losing existing slab slots on OOM and incorrect layout-aware release.
#[test]
fn private_heap_uses_existing_slots_without_requesting_pages() {
    let f = KernelFixture::new();
    let layout = Layout::from_size_align(24, 8).unwrap();
    let first = f.heap.alloc(layout).unwrap();
    f.heap.source.fail_next.store(true, Ordering::Release);
    let second = f.heap.alloc(layout).unwrap();
    assert_ne!(first, second);
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 1);
    assert_eq!(f.heap.heap_stats().live_objects, 2);
    assert!(f.heap.source.fail_next.load(Ordering::Acquire));
    unsafe {
        f.heap.dealloc(first.as_ptr(), layout);
        f.heap.dealloc(second.as_ptr(), layout);
    }
    assert_eq!(f.heap.heap_stats().backing_bytes, 0);
}

#[test]
fn c_requests_and_failed_realloc_preserve_old_allocation() {
    let f = KernelFixture::new();
    assert!(f.heap.malloc(0).is_null());
    assert!(f.heap.malloc_align(17, 3).is_null());
    assert!(f.heap.calloc(usize::MAX, 2).is_null());
    let old = f.heap.malloc_align(63, 64);
    assert!(!old.is_null());
    unsafe {
        old.write_bytes(0x5a, 63);
    }
    f.heap.source.fail_next.store(true, Ordering::Release);
    let result = unsafe { f.heap.c_realloc(old, 8193) };
    assert!(result.is_null());
    for i in 0..63 {
        assert_eq!(unsafe { old.add(i).read() }, 0x5a);
    }
    assert_eq!(f.heap.heap_stats().live_objects, 1);
    let zeroed = f.heap.calloc(17, 19);
    assert!(!zeroed.is_null());
    for i in 0..17 * 19 {
        assert_eq!(unsafe { zeroed.add(i).read() }, 0);
    }
    unsafe {
        f.heap.free(old);
        f.heap.free(zeroed);
    }
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
}

#[test]
fn realloc_moves_preserving_data_and_alignment() {
    let f = KernelFixture::new();
    let layout = Layout::from_size_align(63, 64).unwrap();
    let old = f.heap.alloc(layout).unwrap();
    unsafe {
        old.as_ptr().write_bytes(0x37, 63);
    }
    let new = unsafe { f.heap.realloc(old.as_ptr(), layout, 8193) }.unwrap();
    assert_eq!(new.as_ptr().addr() % 64, 0);
    for i in 0..63 {
        assert_eq!(unsafe { new.as_ptr().add(i).read() }, 0x37);
    }
    assert!(f.heap.size_of_allocation(new) >= 8193);
    unsafe {
        f.heap
            .dealloc(new.as_ptr(), Layout::from_size_align(8193, 64).unwrap());
    }
}

#[test]
fn c_realloc_null_zero_and_large_alignment() {
    let f = KernelFixture::new();
    let p = unsafe { f.heap.c_realloc(core::ptr::null_mut(), 37) };
    assert!(!p.is_null());
    assert!(unsafe { f.heap.c_realloc(p, 0) }.is_null());
    let p = f.heap.malloc_align(8193, 65536);
    assert!(!p.is_null());
    unsafe {
        p.write_bytes(0x4c, 8193);
    }
    let q = unsafe { f.heap.c_realloc(p, 20000) };
    assert!(!q.is_null());
    assert_eq!(q.addr() % 65536, 0);
    for i in 0..8193 {
        assert_eq!(unsafe { q.add(i).read() }, 0x4c);
    }
    unsafe {
        f.heap.free_align(q, 65536);
        f.heap.free(core::ptr::null_mut());
    }
}

// A smaller slab layout must remain valid for a later Rust deallocation.
#[test]
fn realloc_shrinks_slab_and_accepts_new_layout() {
    let f = KernelFixture::new();
    let old = Layout::from_size_align(63, 8).unwrap();
    let ptr = f.heap.alloc(old).unwrap();
    unsafe {
        ptr.as_ptr().write_bytes(0x27, 12);
    }
    let resized = unsafe { f.heap.realloc(ptr.as_ptr(), old, 12) }.unwrap();
    assert_eq!(resized, ptr);
    for i in 0..12 {
        assert_eq!(unsafe { resized.as_ptr().add(i).read() }, 0x27);
    }
    unsafe {
        f.heap
            .dealloc(resized.as_ptr(), Layout::from_size_align(12, 8).unwrap());
    }
    assert_eq!(f.heap.source.live_pages.load(Ordering::Acquire), 0);
}

#[test]
fn frame_summary_excludes_reservations_from_allocatable_total() {
    let info = memory_info_from_frames(FrameStats {
        total: 100,
        reserved: 10,
        allocated: 20,
        free: 70,
        peak_allocated: 30,
    });
    assert_eq!(info.total, 90 * PAGE_SIZE);
    assert_eq!(info.used, 20 * PAGE_SIZE);
    assert_eq!(info.max_used, 30 * PAGE_SIZE);
}

#[test]
fn memory_queries_read_source_outside_heap_lock_and_keep_slab_capacity() {
    let f = KernelFixture::new();
    let layout = Layout::from_size_align(24, 8).unwrap();
    let ptr = f.heap.alloc(layout).unwrap();
    let stats = f.heap.source.frame_stats();
    let info = f.heap.memory_info();
    assert_eq!(info.total, (stats.total - stats.reserved) * PAGE_SIZE);
    // Other kernel allocations can change physical usage between snapshots.
    assert!(info.used >= PAGE_SIZE);
    f.heap
        .source
        .free_run_override
        .store(8192, Ordering::Release);
    assert_eq!(f.heap.get_max_free_block_size(), 8192);
    f.heap.source.free_run_override.store(0, Ordering::Release);
    assert_eq!(f.heap.get_max_free_block_size(), 32);
    let second = f.heap.alloc(layout).unwrap();
    unsafe {
        f.heap.dealloc(ptr.as_ptr(), layout);
        f.heap.dealloc(second.as_ptr(), layout);
    }
    assert_eq!(f.heap.get_max_free_block_size(), 0);
}
