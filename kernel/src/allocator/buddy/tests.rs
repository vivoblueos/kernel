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

use super::heap::BuddyHeap;
use crate::{
    mm::{kernel_phys_to_virt, kernel_virt_to_phys},
    scheduler,
    types::Arc,
};
use alloc::{
    alloc::{alloc, dealloc},
    boxed::Box,
    vec::Vec,
};
use allocator_crate::buddy::{
    order_of_size, BuddyAllocator, BuddyInitError, BuddyMemoryInfo, PageFrame, MAX_ORDER,
    PAGE_SHIFT, PAGE_SIZE,
};
use blueos_test_macro::test;
use core::{
    alloc::Layout,
    ops::Range,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// Total number of pages tracked by the default raw buddy allocator fixture.
const RAW_TEST_PAGES: usize = 512;
/// Number of leading pages excluded from allocation and treated as reserved.
const RAW_TEST_RESERVED: usize = 7;

/// Owns an aligned memory allocation used as backing storage by test fixtures.
///
/// The original layout is retained for correct deallocation.
struct TestAllocation {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl TestAllocation {
    fn new(layout: Layout) -> Self {
        let ptr = NonNull::new(unsafe { alloc(layout) }).expect("test allocation failed");
        Self { ptr, layout }
    }

    fn ptr(&self) -> NonNull<u8> {
        self.ptr
    }
}

impl Drop for TestAllocation {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr.as_ptr(), self.layout) };
    }
}

/// Provides initialized, independently owned state for raw buddy allocator algorithm tests.
/// These tests exercise the allocator directly without involving kernel memory management.
///
/// Field order is intentional: Rust drops fields in declaration order, so the
/// allocator and all of its intrusive list sentinels are destroyed before the
/// metadata allocation they point into is released.
struct RawBuddyFixture {
    buddy: Box<BuddyAllocator>,
    metadata: TestAllocation,
    manageable: Range<usize>,
}

impl RawBuddyFixture {
    fn new() -> Self {
        Self::with_range(RAW_TEST_PAGES, RAW_TEST_RESERVED..RAW_TEST_PAGES)
    }

    fn with_range(total_pages: usize, manageable: Range<usize>) -> Self {
        let layout = BuddyAllocator::metadata_layout(total_pages).unwrap();
        let metadata = TestAllocation::new(layout);
        let mut buddy = Box::new(BuddyAllocator::new());
        unsafe {
            buddy
                .init(
                    metadata.ptr(),
                    layout.size(),
                    total_pages,
                    manageable.clone(),
                )
                .unwrap();
        }
        Self {
            buddy,
            metadata,
            manageable,
        }
    }

    fn assert_conservation(&self) {
        assert_conservation(self.buddy.memory_info());
        assert_eq!(
            self.buddy.memory_info().reserved_pages,
            self.buddy.memory_info().total_pages - self.manageable.len()
        );
    }

    /// Asserts that `allocated` satisfies the buddy-allocator invariants:
    ///
    /// - **In bounds**: every block lies entirely within `self.manageable`.
    /// - **Aligned**: each block's start is a multiple of its own size
    ///   (`2^order` pages).
    /// - **Non-overlapping**: no two blocks share a page.
    /// - **Conservation**: total pages == free + used + reserved, and
    ///   reserved == total - manageable length.
    fn assert_allocations(&self, allocated: &[(PageFrame, usize)]) {
        for (index, &(frame, order)) in allocated.iter().enumerate() {
            let start = frame.pfn();
            let end = start + (1 << order);
            assert!(start >= self.manageable.start);
            assert!(end <= self.manageable.end);
            assert_eq!(start & ((1 << order) - 1), 0);

            for &(other, other_order) in &allocated[..index] {
                let other_start = other.pfn();
                let other_end = other_start + (1 << other_order);
                assert!(end <= other_start || other_end <= start);
            }
        }
        self.assert_conservation();
    }
}

fn assert_conservation(info: BuddyMemoryInfo) {
    assert_eq!(
        info.total_pages,
        info.free_pages + info.used_pages + info.reserved_pages
    );
}

/// Provides a local `BuddyHeap` and real page-aligned memory for wrapper tests.
///
/// The global allocator owns the complete arena as one live allocation. The
/// local buddy only sub-allocates the data pages after the metadata prefix, so
/// local heaps cannot overlap even when several fixtures run concurrently.
/// Field order keeps the heap alive no longer than the backing allocation.
struct BuddyTestArena {
    heap: Box<BuddyHeap>,
    backing: TestAllocation,
    phys_base: usize,
    total_pages: usize,
    manageable_start_pfn: usize,
}

impl BuddyTestArena {
    fn new(total_pages: usize) -> Self {
        assert!(total_pages.is_power_of_two());
        let arena_size = total_pages.checked_mul(PAGE_SIZE).unwrap();
        let arena_layout = Layout::from_size_align(arena_size, PAGE_SIZE).unwrap();
        let backing = TestAllocation::new(arena_layout);
        let metadata_layout = BuddyAllocator::metadata_layout(total_pages).unwrap();
        let manageable_start_pfn = metadata_layout.size().div_ceil(PAGE_SIZE);
        assert!(manageable_start_pfn < total_pages);

        let phys_base = kernel_virt_to_phys(backing.ptr().as_ptr() as usize);
        let heap = Box::new(BuddyHeap::new());
        unsafe {
            heap.init_for_test(
                phys_base,
                total_pages,
                manageable_start_pfn,
                backing.ptr(),
                metadata_layout.size(),
            )
            .unwrap();
        }

        Self {
            heap,
            backing,
            phys_base,
            total_pages,
            manageable_start_pfn,
        }
    }

    fn manageable_phys_start(&self) -> usize {
        self.phys_base + (self.manageable_start_pfn << PAGE_SHIFT)
    }

    fn phys_end(&self) -> usize {
        self.phys_base + (self.total_pages << PAGE_SHIFT)
    }

    fn test_phys_to_virt(&self, phys_addr: usize) -> *mut u8 {
        assert!(phys_addr >= self.manageable_phys_start());
        assert!(phys_addr < self.phys_end());
        let virt = kernel_phys_to_virt(phys_addr) as *mut u8;
        let arena_start = self.backing.ptr().as_ptr() as usize;
        assert!((virt as usize) >= arena_start);
        assert!((virt as usize) < arena_start + self.backing.layout.size());
        virt
    }
}

/// Verifies that an uninitialized raw allocator reports zero pages in every category.
#[test]
fn raw_uninitialized_memory_info_is_empty() {
    assert_eq!(
        BuddyAllocator::new().memory_info(),
        BuddyMemoryInfo {
            total_pages: 0,
            free_pages: 0,
            used_pages: 0,
            reserved_pages: 0,
        }
    );
}

/// Verifies page accounting when only an arbitrary subrange is manageable.
#[test]
fn raw_init_accounts_for_arbitrary_manageable_range() {
    let fixture = RawBuddyFixture::with_range(37, 3..34);
    let info = fixture.buddy.memory_info();
    assert_eq!(info.total_pages, 37);
    assert_eq!(info.free_pages, 31);
    assert_eq!(info.used_pages, 0);
    assert_eq!(info.reserved_pages, 6);
    fixture.assert_conservation();
}

/// Verifies that metadata sizing and initialization reject invalid inputs.
#[test]
fn raw_metadata_layout_and_init_reject_invalid_inputs() {
    assert_eq!(
        BuddyAllocator::metadata_layout(0),
        Err(BuddyInitError::ZeroPages)
    );
    assert_eq!(
        BuddyAllocator::metadata_layout(usize::MAX),
        Err(BuddyInitError::MetadataLayoutOverflow)
    );

    let layout = BuddyAllocator::metadata_layout(8).unwrap();
    let raw_layout =
        Layout::from_size_align(layout.size() + layout.align(), layout.align()).unwrap();
    let metadata = TestAllocation::new(raw_layout);

    let mut short = Box::new(BuddyAllocator::new());
    assert_eq!(
        unsafe { short.init(metadata.ptr(), layout.size() - 1, 8, 0..8) },
        Err(BuddyInitError::MetadataTooSmall {
            required: layout.size(),
            provided: layout.size() - 1,
        })
    );

    let mut misaligned = Box::new(BuddyAllocator::new());
    let shifted = NonNull::new(unsafe { metadata.ptr().as_ptr().add(1) }).unwrap();
    assert_eq!(
        unsafe { misaligned.init(shifted, layout.size(), 8, 0..8) },
        Err(BuddyInitError::MetadataMisaligned)
    );

    let mut invalid_range = Box::new(BuddyAllocator::new());
    let invalid_start = 7;
    let invalid_end = 6;
    assert_eq!(
        unsafe { invalid_range.init(metadata.ptr(), layout.size(), 8, invalid_start..invalid_end) },
        Err(BuddyInitError::InvalidManageableRange)
    );
    assert_eq!(
        unsafe { invalid_range.init(metadata.ptr(), layout.size(), 8, 0..9) },
        Err(BuddyInitError::InvalidManageableRange)
    );

    let mut initialized = Box::new(BuddyAllocator::new());
    unsafe {
        initialized
            .init(metadata.ptr(), layout.size(), 8, 2..8)
            .unwrap();
    }
    assert_eq!(
        unsafe { initialized.init(metadata.ptr(), layout.size(), 8, 2..8) },
        Err(BuddyInitError::AlreadyInitialized)
    );
}

/// Verifies allocation, alignment, accounting, and freeing for every supported order.
#[test]
fn raw_allocates_and_frees_every_supported_order() {
    let pages = 1 << MAX_ORDER;
    let mut fixture = RawBuddyFixture::with_range(pages, 0..pages);
    let before = fixture.buddy.memory_info();

    for order in 0..=MAX_ORDER {
        let frame = fixture.buddy.alloc_pages(order).expect("allocation");
        assert_eq!(frame.pfn() & ((1 << order) - 1), 0);
        assert_eq!(
            fixture.buddy.memory_info().free_pages,
            before.free_pages - (1 << order)
        );
        unsafe { fixture.buddy.free_pages(frame, order) };
        assert_eq!(fixture.buddy.memory_info(), before);
    }

    assert!(fixture.buddy.alloc_pages(MAX_ORDER + 1).is_none());
    assert!(fixture
        .buddy
        .alloc_pages_aligned(0, MAX_ORDER + 1)
        .is_none());
    fixture.assert_conservation();
}

/// Verifies that aligned allocation honors an alignment larger than the block size.
#[test]
fn raw_aligned_allocation_honors_requested_alignment() {
    let mut fixture = RawBuddyFixture::with_range(64, 0..64);
    let before = fixture.buddy.memory_info();
    let frame = fixture.buddy.alloc_pages_aligned(1, 4).unwrap();
    assert_eq!(frame.pfn() & ((1 << 4) - 1), 0);
    assert_eq!(fixture.buddy.memory_info().used_pages, 2);
    unsafe { fixture.buddy.free_pages(frame, 1) };
    assert_eq!(fixture.buddy.memory_info(), before);
}

/// Verifies that page-by-page exhaustion and recovery neither lose nor leak pages.
#[test]
fn raw_exhaustion_recovers_without_leaking() {
    let mut fixture = RawBuddyFixture::new();
    let before = fixture.buddy.memory_info();
    let mut frames = Vec::new();
    while let Some(frame) = fixture.buddy.alloc_pages(0) {
        frames.push(frame);
    }
    assert_eq!(frames.len(), before.free_pages);
    assert_eq!(fixture.buddy.memory_info().free_pages, 0);
    assert!(fixture.buddy.alloc_pages(0).is_none());

    for frame in frames {
        unsafe { fixture.buddy.free_pages(frame, 0) };
    }
    assert_eq!(fixture.buddy.memory_info(), before);
    fixture.assert_conservation();
}

/// Verifies that freed buddy pages coalesce into a larger allocatable block.
#[test]
fn raw_coalesces_buddies_for_a_larger_allocation() {
    let mut fixture = RawBuddyFixture::with_range(16, 0..16);
    let first = fixture.buddy.alloc_pages(0).unwrap();
    let second = fixture.buddy.alloc_pages(0).unwrap();
    assert_eq!(first.pfn() ^ second.pfn(), 1);
    unsafe {
        fixture.buddy.free_pages(second, 0);
        fixture.buddy.free_pages(first, 0);
    }

    let whole = fixture.buddy.alloc_pages(4).unwrap();
    assert_eq!(whole.pfn(), 0);
    unsafe { fixture.buddy.free_pages(whole, 4) };
    fixture.assert_conservation();
}

/// Verifies that different free orders all restore the allocator's initial state.
#[test]
fn raw_free_orders_all_restore_the_initial_state() {
    for mode in 0..3 {
        let mut fixture = RawBuddyFixture::with_range(32, 0..32);
        let before = fixture.buddy.memory_info();
        let mut frames = Vec::new();
        while let Some(frame) = fixture.buddy.alloc_pages(0) {
            frames.push(frame);
        }
        match mode {
            0 => {}
            1 => frames.reverse(),
            2 => {
                let mut interleaved = Vec::with_capacity(frames.len());
                while !frames.is_empty() {
                    interleaved.push(frames.remove(frames.len() / 2));
                }
                frames = interleaved;
            }
            _ => unreachable!(),
        }
        for frame in frames {
            unsafe { fixture.buddy.free_pages(frame, 0) };
        }
        assert_eq!(fixture.buddy.memory_info(), before);
    }
}

/// Verifies that coalescing never crosses the boundaries of the manageable range.
#[test]
fn raw_coalescing_stays_inside_the_manageable_range() {
    let mut fixture = RawBuddyFixture::with_range(16, 1..15);
    let before = fixture.buddy.memory_info();
    let mut frames = Vec::new();
    while let Some(frame) = fixture.buddy.alloc_pages(0) {
        assert!((1..15).contains(&frame.pfn()));
        frames.push(frame);
    }
    for frame in frames {
        unsafe { fixture.buddy.free_pages(frame, 0) };
    }
    assert_eq!(fixture.buddy.memory_info(), before);
    assert!(fixture.buddy.alloc_pages(3).is_none());
    fixture.assert_conservation();
}

/// Verifies mixed allocations and frees against an independent page-occupancy model.
#[test]
fn raw_deterministic_mixed_sequence_matches_reference_model() {
    let mut fixture = RawBuddyFixture::with_range(128, 5..123);
    let before = fixture.buddy.memory_info();
    let mut allocated: Vec<(PageFrame, usize)> = Vec::new();
    let mut occupied = [false; 128];
    let mut random = 0x7a5b_39d1_u32;

    for _ in 0..512 {
        random ^= random << 13;
        random ^= random >> 17;
        random ^= random << 5;

        let should_free = !allocated.is_empty() && random & 3 == 0;
        if should_free {
            let index = random as usize % allocated.len();
            let (frame, order) = allocated.swap_remove(index);
            let end = frame.pfn() + (1 << order);
            for used in &mut occupied[frame.pfn()..end] {
                assert!(*used);
                *used = false;
            }
            unsafe { fixture.buddy.free_pages(frame, order) };
        } else {
            let order = (random as usize >> 8) % 5;
            if let Some(frame) = fixture.buddy.alloc_pages(order) {
                let end = frame.pfn() + (1 << order);
                for used in &mut occupied[frame.pfn()..end] {
                    assert!(!*used);
                    *used = true;
                }
                allocated.push((frame, order));
            }
        }

        fixture.assert_allocations(&allocated);
        assert_eq!(
            fixture.buddy.memory_info().used_pages,
            occupied.iter().filter(|&&used| used).count()
        );
    }

    for (frame, order) in allocated {
        unsafe { fixture.buddy.free_pages(frame, order) };
    }
    assert_eq!(fixture.buddy.memory_info(), before);
}

/// Verifies order calculation at page-size boundaries and at the maximum input size.
#[test]
fn order_of_size_covers_page_boundaries() {
    assert_eq!(order_of_size(0), 0);
    assert_eq!(order_of_size(1), 0);
    assert_eq!(order_of_size(PAGE_SIZE), 0);
    assert_eq!(order_of_size(PAGE_SIZE + 1), 1);
    assert_eq!(order_of_size(2 * PAGE_SIZE), 1);
    assert_eq!(order_of_size(3 * PAGE_SIZE), 2);
    assert_eq!(order_of_size(4 * PAGE_SIZE), 2);
    assert_eq!(order_of_size(usize::MAX), usize::BITS as usize - PAGE_SHIFT);
}

/// Verifies wrapper address translation, alignment checks, bounds checks, and overflow handling.
#[test]
fn wrapper_translates_addresses_and_handles_overflow() {
    let layout = BuddyAllocator::metadata_layout(2).unwrap();
    let metadata = TestAllocation::new(layout);
    let heap = Box::new(BuddyHeap::new());
    let phys_base = usize::MAX & !(PAGE_SIZE - 1);
    unsafe {
        heap.init_for_test(phys_base, 2, 0, metadata.ptr(), layout.size())
            .unwrap();
    }

    assert_eq!(heap.pfn_to_phys(0), Some(phys_base));
    assert_eq!(heap.pfn_to_phys(1), None);
    assert_eq!(heap.pfn_to_phys(2), None);
    assert_eq!(heap.phys_to_pfn(phys_base), Some(0));
    assert_eq!(heap.phys_to_pfn(phys_base + 1), None);
    assert_eq!(heap.phys_to_pfn(phys_base - PAGE_SIZE), None);
}

/// Verifies wrapper allocation, translation, and data access using real backing memory.
#[test]
fn wrapper_reads_and_writes_real_backing_pages() {
    let arena = BuddyTestArena::new(16);
    let before = arena.heap.memory_info();
    let last_phys = arena.phys_base + ((arena.total_pages - 1) << PAGE_SHIFT);
    assert_eq!(arena.heap.phys_to_pfn(arena.phys_base), Some(0));
    assert_eq!(
        arena.heap.phys_to_pfn(last_phys),
        Some(arena.total_pages - 1)
    );
    assert_eq!(
        arena.heap.pfn_to_phys(arena.total_pages - 1),
        Some(last_phys)
    );
    assert_eq!(arena.heap.phys_to_pfn(arena.phys_base + 1), None);
    assert_eq!(arena.heap.phys_to_pfn(arena.phys_end()), None);
    assert_eq!(arena.heap.pfn_to_phys(arena.total_pages), None);

    let first_phys = arena.heap.alloc_pages_phys_addr(0).unwrap();
    let block_phys = arena.heap.alloc_pages_phys_addr(2).unwrap();
    let first = arena.test_phys_to_virt(first_phys);
    let block = arena.test_phys_to_virt(block_phys);

    assert!(first_phys >= arena.manageable_phys_start());
    assert_eq!(block_phys & ((PAGE_SIZE << 2) - 1), 0);
    assert!(first_phys + PAGE_SIZE <= block_phys || block_phys + (PAGE_SIZE << 2) <= first_phys);
    unsafe {
        first.write(0x11);
        first.add(PAGE_SIZE - 1).write(0x22);
        block.write(0x33);
        block.add(PAGE_SIZE).write(0x44);
        block.add((PAGE_SIZE << 2) - 1).write(0x55);

        assert_eq!(first.read(), 0x11);
        assert_eq!(first.add(PAGE_SIZE - 1).read(), 0x22);
        assert_eq!(block.read(), 0x33);
        assert_eq!(block.add(PAGE_SIZE).read(), 0x44);
        assert_eq!(block.add((PAGE_SIZE << 2) - 1).read(), 0x55);
    }

    unsafe { arena.heap.free_pages_phys_addr(first_phys, 0) };
    unsafe {
        assert_eq!(block.read(), 0x33);
        assert_eq!(block.add((PAGE_SIZE << 2) - 1).read(), 0x55);
        arena.heap.free_pages_phys_addr(block_phys, 2);
    }
    assert_eq!(arena.heap.memory_info(), before);
}

/// Verifies that independent local buddy arenas operate correctly in concurrent threads.
#[test]
fn independent_local_arenas_can_run_concurrently() {
    let done = Arc::new(AtomicUsize::new(0));
    for worker in 0..2 {
        let done = done.clone();
        crate::thread::spawn(move || {
            let arena = BuddyTestArena::new(16);
            let before = arena.heap.memory_info();
            for iteration in 0..32 {
                let phys = arena.heap.alloc_pages_phys_addr(0).unwrap();
                let ptr = arena.test_phys_to_virt(phys);
                let pattern = (worker * 32 + iteration) as u8;
                unsafe {
                    ptr.write(pattern);
                    assert_eq!(ptr.read(), pattern);
                    arena.heap.free_pages_phys_addr(phys, 0);
                }
                scheduler::yield_me();
            }
            assert_eq!(arena.heap.memory_info(), before);
            done.fetch_add(1, Ordering::Release);
        })
        .expect("failed to spawn local buddy test worker");
    }
    while done.load(Ordering::Acquire) != 2 {
        scheduler::yield_me();
    }
}

/// Verifies that concurrent operations on one local buddy heap are serialized safely.
#[test]
fn shared_local_heap_serializes_concurrent_operations() {
    let arena = Arc::new(BuddyTestArena::new(32));
    let before = arena.heap.memory_info();
    let done = Arc::new(AtomicUsize::new(0));

    for worker in 0..2 {
        let arena = arena.clone();
        let done = done.clone();
        crate::thread::spawn(move || {
            for iteration in 0..64 {
                let phys = arena.heap.alloc_pages_phys_addr(0).unwrap();
                let ptr = arena.test_phys_to_virt(phys);
                let pattern = (worker * 64 + iteration) as u8;
                unsafe { ptr.write(pattern) };
                scheduler::yield_me();
                assert_eq!(unsafe { ptr.read() }, pattern);
                unsafe { arena.heap.free_pages_phys_addr(phys, 0) };
            }
            done.fetch_add(1, Ordering::Release);
        })
        .expect("failed to spawn shared buddy test worker");
    }

    while done.load(Ordering::Acquire) != 2 {
        scheduler::yield_me();
    }
    assert_eq!(arena.heap.memory_info(), before);
}
