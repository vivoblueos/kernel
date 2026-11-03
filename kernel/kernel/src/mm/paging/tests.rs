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

use super::{AllocatorState, FirstFitFrameAllocator, FrameState};
use crate::mm::{
    kernel_phys_to_virt, kernel_virt_to_phys,
    memory_bank::MemoryRegion,
    paging::{mapper::PageMapper, FrameDeallocationError, FrameStats, PageFormat},
    CachePolicy, MemAttribute, MemFlags, MemType, PhysicalAddress, VirtualAddress,
};
use alloc::{alloc::Layout, boxed::Box};
use blueos_test_macro::test;
use core::ptr::NonNull;

const PAGE_SIZE: usize = 4096;

/// Private suballocator over exclusively owned, physically contiguous frame
/// backing. Its state and backing outlive every allocation used by each test.
#[must_use]
struct Fixture<const N: usize> {
    allocator: FirstFitFrameAllocator,
    _states: Box<[FrameState; N]>,
    backing: NonNull<u8>,
    layout: Layout,
    managed_base: PhysicalAddress,
}

impl<const N: usize> Fixture<N> {
    // Test allocators own private metadata instead of reinitializing the
    // kernel's global STATES through the boot-only init interface.
    fn allocator(
        base: PhysicalAddress,
        states: &'static mut [FrameState],
    ) -> FirstFitFrameAllocator {
        let free = states.iter().filter(|s| **s == FrameState::Free).count();
        let reserved = states
            .iter()
            .filter(|s| **s == FrameState::Reserved)
            .count();
        let allocated = states.len() - free - reserved;
        let first_free = states
            .iter()
            .position(|s| *s == FrameState::Free)
            .unwrap_or(states.len());
        FirstFitFrameAllocator {
            state: crate::sync::SpinLock::new(Some(AllocatorState {
                base: base.into_raw(),
                page_size: PAGE_SIZE,
                states,
                first_free,
                reserved,
                allocated,
                free,
                peak_allocated: allocated,
            })),
        }
    }

    fn new(states: [FrameState; N]) -> Self {
        let layout = Layout::from_size_align(N * PAGE_SIZE, PAGE_SIZE).unwrap();
        let physical = FirstFitFrameAllocator::instance()
            .alloc_frames(N)
            .expect("fixture physical backing");
        let backing = NonNull::new(kernel_phys_to_virt(physical).into_raw() as *mut u8).unwrap();
        let mut states = Box::new(states);
        let base = kernel_virt_to_phys(VirtualAddress::new(backing.as_ptr() as usize));
        // SAFETY: the fixture owns stable backing and metadata allocations. All
        // returned frames are released before fixture teardown, and metadata
        // outlives the allocator field.
        let allocator =
            unsafe { Self::allocator(base, &mut *(&mut *states as *mut [FrameState; N])) };
        Self {
            allocator,
            _states: states,
            backing,
            layout,
            managed_base: base,
        }
    }

    fn with_misaligned_base(states: [FrameState; N]) -> Self {
        let layout = Layout::from_size_align((N + 1) * PAGE_SIZE, PAGE_SIZE).unwrap();
        let physical = FirstFitFrameAllocator::instance()
            .alloc_frames(N + 1)
            .unwrap();
        let backing = NonNull::new(kernel_phys_to_virt(physical).into_raw() as *mut u8).unwrap();
        let physical = kernel_virt_to_phys(VirtualAddress::new(backing.as_ptr() as usize));
        let skip = usize::from((physical.into_raw() & (4 * PAGE_SIZE - 1)) == 0);
        let managed_base = PhysicalAddress::new(physical.into_raw() + skip * PAGE_SIZE);
        let mut states = Box::new(states);
        // SAFETY: the N-page managed window lies inside this fixture's N+1
        // backing pages, with the same lifetime guarantees as `new`.
        let allocator =
            unsafe { Self::allocator(managed_base, &mut *(&mut *states as *mut [FrameState; N])) };
        Self {
            allocator,
            _states: states,
            backing,
            layout,
            managed_base,
        }
    }

    fn base(&self) -> PhysicalAddress {
        self.managed_base
    }

    fn frame(&self, index: usize) -> PhysicalAddress {
        PhysicalAddress::new(self.base().into_raw() + index * PAGE_SIZE)
    }
}

impl<const N: usize> Drop for Fixture<N> {
    fn drop(&mut self) {
        // All guards borrow this fixture and have already been dropped.
        unsafe {
            FirstFitFrameAllocator::instance()
                .free_frames(
                    kernel_virt_to_phys(VirtualAddress::new(self.backing.as_ptr() as usize)),
                    self.layout.size() / PAGE_SIZE,
                )
                .unwrap();
        }
    }
}

#[test]
fn aligned_runs_use_absolute_physical_alignment() {
    let fixture = Fixture::with_misaligned_base([FrameState::Free; 8]);
    let allocator = &fixture.allocator;
    assert_ne!(fixture.base().into_raw() % (4 * PAGE_SIZE), 0);
    let run = allocator.alloc_owned_frames_aligned(2, 4).unwrap();
    assert_eq!(run.address().into_raw() % (4 * PAGE_SIZE), 0);
    let stats = allocator.frame_stats().unwrap();
    assert_eq!(
        (stats.allocated, stats.free, stats.peak_allocated),
        (2, 6, 2)
    );
    drop(run);
    let after = allocator.frame_stats().unwrap();
    assert_eq!(
        (after.allocated, after.free, after.peak_allocated),
        (0, 8, 2)
    );
}

#[test]
fn aligned_search_preserves_skipped_frames_on_success_and_failure() {
    let fixture = Fixture::with_misaligned_base([FrameState::Free; 8]);
    let allocator = &fixture.allocator;
    let before = allocator.frame_stats().unwrap();
    assert!(allocator.alloc_frames_aligned(8, 4).is_none());
    assert_eq!(allocator.frame_stats().unwrap(), before);
    let run = allocator.alloc_owned_frames_aligned(2, 4).unwrap();
    let first = allocator.alloc_owned_frames(1).unwrap();
    assert_eq!(first.address(), fixture.base());
    drop(first);
    drop(run);
    assert_eq!(allocator.frame_stats().unwrap().free, 8);
}

#[test]
fn invalid_alignment_does_not_consume_frames() {
    let fixture = Fixture::new([FrameState::Free; 8]);
    let allocator = &fixture.allocator;
    let before = allocator.frame_stats().unwrap();
    assert!(allocator.alloc_frames_aligned(1, 0).is_none());
    assert!(allocator.alloc_frames_aligned(1, 3).is_none());
    assert!(allocator.alloc_frames_aligned(usize::MAX, 1).is_none());
    assert!(allocator.alloc_frames_aligned(0, 1).is_none());
    assert!(allocator
        .alloc_frames_aligned(1, 1usize << (usize::BITS - 1))
        .is_none());
    assert_eq!(allocator.frame_stats().unwrap(), before);
    assert_eq!(
        allocator.alloc_owned_frames(1).unwrap().address(),
        fixture.base()
    );
}

#[test]
fn reserved_holes_bound_free_runs_and_preserve_statistics() {
    use FrameState::{Free as F, Reserved as R};
    let fixture = Fixture::new([F, R, F, F, R, F]);
    let allocator = &fixture.allocator;
    let initial = FrameStats {
        total: 6,
        reserved: 2,
        allocated: 0,
        free: 4,
        peak_allocated: 0,
    };
    assert_eq!(allocator.frame_stats().unwrap(), initial);
    assert_eq!(allocator.usage().unwrap().used(), 2);
    assert_eq!(allocator.largest_free_run(), Some(2));
    assert!(allocator.alloc_frames_aligned(3, 1).is_none());
    assert_eq!(allocator.frame_stats().unwrap(), initial);
    let run = allocator.alloc_owned_frames_aligned(2, 1).unwrap();
    assert_eq!(run.address(), fixture.frame(2));
    assert_eq!(allocator.largest_free_run(), Some(1));
    assert_eq!(allocator.usage().unwrap().used(), 4);
    let allocated = FrameStats {
        allocated: 2,
        free: 2,
        peak_allocated: 2,
        ..initial
    };
    assert_eq!(allocator.frame_stats().unwrap(), allocated);
    assert_eq!(
        unsafe { allocator.free_frames(run.address(), 3) },
        Err(FrameDeallocationError::Reserved)
    );
    assert_eq!(allocator.frame_stats().unwrap(), allocated);
    let first = allocator.alloc_owned_frames(1).unwrap();
    assert_eq!(first.address(), fixture.base());
    drop(first);
    drop(run);
    assert_eq!(allocator.largest_free_run(), Some(2));
    assert_eq!(
        allocator.frame_stats().unwrap(),
        FrameStats {
            peak_allocated: 3,
            ..initial
        }
    );
}

#[test]
fn frame_statistics_track_initial_allocations_and_empty_free_runs() {
    let fresh = FirstFitFrameAllocator::new();
    assert_eq!(fresh.frame_stats(), None);
    assert_eq!(fresh.largest_free_run(), None);
    use FrameState::{Allocated as A, Reserved as R};
    let fixture = Fixture::new([R, A]);
    let allocator = &fixture.allocator;
    assert_eq!(
        allocator.frame_stats(),
        Some(FrameStats {
            total: 2,
            reserved: 1,
            allocated: 1,
            free: 0,
            peak_allocated: 1,
        })
    );
    assert_eq!(allocator.largest_free_run(), Some(0));
    unsafe { allocator.free_frame(fixture.frame(1)).unwrap() };
    assert_eq!(
        allocator.frame_stats(),
        Some(FrameStats {
            total: 2,
            reserved: 1,
            allocated: 0,
            free: 1,
            peak_allocated: 1,
        })
    );
    assert_eq!(allocator.largest_free_run(), Some(1));
}

// Region generation uses a fixed-capacity list larger than the default
// test thread's stack, so run these checks on a dedicated stack.
fn with_region_stack(check: impl FnOnce() + Send + 'static) {
    use crate::{
        sync::ConstBarrier,
        thread::{Builder, Entry, Stack},
        types::Arc,
    };
    let done = Arc::new(ConstBarrier::<2>::new());
    let worker_done = done.clone();
    let _worker = Builder::new(Entry::Closure(Box::new(move || {
        check();
        worker_done.wait();
    })))
    .set_stack(Stack::from_size(32 * 1024).unwrap())
    .start();
    done.wait();
}

#[test]
fn boot_frame_states_match_disjoint_memory_regions() {
    with_region_stack(|| {
        use crate::mm::memory_bank::create_memory_region_from_memory_bank;
        let regions = create_memory_region_from_memory_bank(crate::boards::MEMORY_BANKS);
        let state = FirstFitFrameAllocator::instance().state.irqsave_lock();
        let state = state
            .as_ref()
            .expect("boot initialized the frame allocator");
        assert_eq!(state.base, crate::boards::PHYS_DRAM_BASE as usize);
        assert_eq!(state.page_size, PAGE_SIZE);
        assert_eq!(
            state.states.len(),
            crate::boards::PHYS_DRAM_SIZE as usize / PAGE_SIZE
        );
        for (index, frame_state) in state.states.iter().enumerate() {
            let frame = state.base + index * PAGE_SIZE;
            let available = regions.iter().any(|region| {
                !region.is_reserved
                    && frame >= region.base.into_raw()
                    && frame + PAGE_SIZE <= region.base.into_raw() + region.size
            });
            // Available RAM may already back live allocations. Image, device
            // and undescribed pages must still be reserved.
            assert_eq!(
                *frame_state == FrameState::Reserved,
                !available,
                "unexpected reservation for physical frame {:#x}",
                frame,
            );
        }
    });
}

#[test]
fn memory_bank_regions_exclude_image_mmio_and_bank_gaps() {
    with_region_stack(|| {
        use crate::mm::memory_bank::{create_memory_region_from_memory_bank, MemoryBank};
        let start = crate::boards::PHYS_DRAM_BASE as usize;
        let end = start + crate::boards::PHYS_DRAM_SIZE as usize;
        let banks = [
            // Put MMIO before RAM to check that bank order does not affect splitting.
            MemoryBank::MMIO((
                PhysicalAddress::new(end - PAGE_SIZE),
                PhysicalAddress::new(end),
            )),
            MemoryBank::MMIO((PhysicalAddress::new(0), PhysicalAddress::new(PAGE_SIZE))),
            MemoryBank::RAM((
                PhysicalAddress::new(end - 2 * PAGE_SIZE),
                PhysicalAddress::new(end),
            )),
            MemoryBank::RAM((
                PhysicalAddress::new(start),
                PhysicalAddress::new(end - 4 * PAGE_SIZE),
            )),
        ];
        let regions = create_memory_region_from_memory_bank(&banks);
        assert!(regions
            .windows(2)
            .all(|pair| { pair[0].base.into_raw() + pair[0].size <= pair[1].base.into_raw() }));
        // Every byte of RAM is described once, except the MMIO outside RAM.
        assert_eq!(
            regions.iter().map(|region| region.size).sum::<usize>(),
            end - start - 2 * PAGE_SIZE + PAGE_SIZE
        );
        let text = regions
            .iter()
            .find(|region| region.name == ".text")
            .unwrap();
        assert!(text.is_reserved);
        assert_eq!(text.flags, MemFlags::READ | MemFlags::EXECUTE);
        let rodata = regions
            .iter()
            .find(|region| region.name == ".rodata")
            .unwrap();
        assert!(rodata.is_reserved);
        assert_eq!(rodata.flags, MemFlags::READ);
        for region in &regions {
            if region.memory_type == MemType::Device {
                assert!(region.is_reserved);
                assert_eq!(region.flags, MemFlags::READ | MemFlags::WRITE);
            }
        }
        let tail = end - 8 * PAGE_SIZE;
        for (index, expected_reserved) in [false, false, false, false, true, true, false, true]
            .into_iter()
            .enumerate()
        {
            let frame = tail + index * PAGE_SIZE;
            let region = regions.iter().find(|region| {
                frame >= region.base.into_raw() && frame < region.base.into_raw() + region.size
            });
            assert_eq!(region.is_none_or(|r| r.is_reserved), expected_reserved);
        }
    });
}

#[test]
fn frame_allocate_free_reuse_and_exhaustion() {
    use FrameState::{Free as F, Reserved as R};
    let fixture = Fixture::new([R, F, F, R, F]);
    let allocator = &fixture.allocator;
    assert_eq!(allocator.usage().unwrap().free(), 3);
    let first = allocator.alloc_frames(2).unwrap();
    assert_eq!(first, fixture.frame(1));
    let last = allocator.alloc_frame().unwrap();
    assert_eq!(last, fixture.frame(4));
    assert!(allocator.alloc_frame().is_none());
    assert_eq!(allocator.usage().unwrap().free(), 0);
    unsafe {
        allocator.free_frames(first, 2).unwrap();
    }
    assert_eq!(allocator.alloc_frame().unwrap(), first);
    unsafe {
        allocator.free_frame(first).unwrap();
        allocator.free_frame(last).unwrap();
    }
    assert_eq!(allocator.usage().unwrap().free(), 3);
}

#[test]
fn frame_contiguous_failure_preserves_fragmented_pages() {
    use FrameState::{Free as F, Reserved as R};
    let fixture = Fixture::new([F, R, F, R, F, F]);
    let allocator = &fixture.allocator;
    assert!(allocator.alloc_frames(3).is_none());
    assert!(allocator.alloc_frames(0).is_none());
    assert!(allocator.alloc_frames(usize::MAX).is_none());
    assert_eq!(allocator.usage().unwrap().free(), 4);
    let run = allocator.alloc_owned_frames(2).unwrap();
    assert_eq!(run.address(), fixture.frame(4));
    let first = allocator.alloc_owned_frames(1).unwrap();
    assert_eq!(first.address(), fixture.frame(0));
    drop(run);
    drop(first);
    assert_eq!(allocator.usage().unwrap().free(), 4);
}

#[test]
fn frame_free_rejects_invalid_reserved_and_duplicate_ranges() {
    use FrameDeallocationError::{InvalidRange, NotAllocated, NotInitialized, Reserved};
    use FrameState::{Free as F, Reserved as R};
    let fresh = FirstFitFrameAllocator::new();
    assert_eq!(
        unsafe { fresh.free_frame(PhysicalAddress::new(0)) },
        Err(NotInitialized)
    );
    let fixture = Fixture::new([F, F, R, F]);
    let allocator = &fixture.allocator;
    let run = allocator.alloc_frames(2).unwrap();
    unsafe {
        for (address, count) in [
            (PhysicalAddress::new(run.into_raw() - 1), 1),
            (PhysicalAddress::new(run.into_raw() + 1), 1),
            (fixture.frame(4), 1),
            (run, 0),
            (run, usize::MAX),
        ] {
            assert_eq!(allocator.free_frames(address, count), Err(InvalidRange));
        }
        assert_eq!(allocator.free_frames(run, 3), Err(Reserved));
        assert_eq!(allocator.usage().unwrap().free(), 1);
        allocator.free_frame(fixture.frame(1)).unwrap();
        assert_eq!(allocator.free_frames(run, 2), Err(NotAllocated));
        assert_eq!(allocator.usage().unwrap().free(), 2);
        allocator.free_frame(run).unwrap();
        assert_eq!(allocator.free_frame(run), Err(NotAllocated));
    }
    assert_eq!(allocator.usage().unwrap().free(), 3);
}

#[test]
fn frame_guards_rollback_and_zero_recycled_user_pages() {
    let fixture = Fixture::new([FrameState::Free; 3]);
    let allocator = &fixture.allocator;
    fn fail(allocator: &FirstFitFrameAllocator) -> Option<()> {
        let _first = allocator.alloc_owned_frames(2)?;
        let _second = allocator.alloc_owned_frames(2)?;
        Some(())
    }
    assert!(fail(allocator).is_none());
    assert_eq!(allocator.usage().unwrap().free(), 3);
    let frame = allocator.alloc_owned_frames(1).unwrap();
    let address = frame.address();
    let bytes = kernel_phys_to_virt(address).into_raw() as *mut u8;
    unsafe {
        bytes.write_bytes(0xa5, PAGE_SIZE);
    }
    drop(frame);
    let zeroed = allocator.alloc_zeroed_frame().unwrap();
    assert_eq!(zeroed.address(), address);
    assert!(unsafe { core::slice::from_raw_parts(bytes, PAGE_SIZE) }
        .iter()
        .all(|b| *b == 0));
    let raw = zeroed.into_raw();
    assert_eq!(allocator.usage().unwrap().free(), 2);
    unsafe {
        allocator.free_frame(raw).unwrap();
    }
    assert_eq!(allocator.usage().unwrap().free(), 3);
}

#[test]
fn page_table_allocation_failure_returns_all_table_frames() {
    let fixture = Fixture::new([FrameState::Free; 2]);
    let allocator = &fixture.allocator;
    for _ in 0..32 {
        let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
        assert!(mapper
            .prepare_range(VirtualAddress::new(0x4000), PAGE_SIZE)
            .is_err());
        assert_eq!(allocator.usage().unwrap().free(), 0);
    }
    assert_eq!(allocator.usage().unwrap().free(), 2);
    {
        let _all = allocator.alloc_owned_frames(2).unwrap();
        assert!(unsafe { PageMapper::<_>::create(allocator) }.is_err());
    }
    assert_eq!(allocator.usage().unwrap().free(), 2);
}

#[test]
fn page_table_cleanup_keeps_leaf_backing_owned_by_caller() {
    let fixture = Fixture::new([FrameState::Free; 8]);
    let allocator = &fixture.allocator;
    let data = allocator.alloc_zeroed_frame().unwrap();
    let data_addr = data.address();
    {
        let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
        mapper
            .map_range(
                VirtualAddress::new(0x8000),
                data_addr,
                PAGE_SIZE,
                MemAttribute {
                    flags: MemFlags::READ | MemFlags::WRITE | MemFlags::USER,
                    memory_type: MemType::Normal(CachePolicy::WriteBack),
                },
            )
            .unwrap();
        assert_eq!(mapper.translate(0x8000), Some(data_addr));
        assert_eq!(
            allocator.usage().unwrap().free(),
            8 - 1 - crate::arch::page::PageEntry::LEVELS as usize
        );
        // A separate branch shares the same data page. Cleanup must walk both
        // branches and must not release either leaf's backing allocation.
        mapper
            .map_range(
                VirtualAddress::new(0x4000_0000),
                data_addr,
                PAGE_SIZE,
                MemAttribute {
                    flags: MemFlags::READ | MemFlags::USER,
                    memory_type: MemType::Normal(CachePolicy::WriteBack),
                },
            )
            .unwrap();
        assert_eq!(mapper.translate(0x4000_0000), Some(data_addr));
        assert_eq!(
            allocator.usage().unwrap().free(),
            8 - 3 - crate::arch::page::PageEntry::LEVELS as usize
        );
    }
    assert_eq!(allocator.usage().unwrap().free(), 7);
    drop(data);
    assert_eq!(allocator.usage().unwrap().free(), 8);
}

#[test]
fn boot_runtime_frames_do_not_overlap_live_heap_buffers() {
    let buffer = alloc::vec![0xa5u8; 2 * PAGE_SIZE];
    let page = FirstFitFrameAllocator::instance()
        .alloc_zeroed_frame()
        .unwrap();
    for offset in (0..buffer.len()).step_by(PAGE_SIZE) {
        let physical =
            kernel_virt_to_phys(VirtualAddress::new(buffer.as_ptr() as usize + offset)).into_raw();
        assert_ne!(page.address().into_raw(), physical);
    }
    assert!(buffer.iter().all(|byte| *byte == 0xa5));
}

#[cfg(target_arch = "aarch64")]
#[test]
fn heap_backing_uses_privileged_non_executable_leaf_entries() {
    let buffer = alloc::vec![0u8; PAGE_SIZE];
    let space = crate::mm::kernel_space::KernelAddressSpace::get().unwrap();
    let entry = space.leaf_descriptor(buffer.as_ptr() as usize).unwrap();
    assert_ne!(entry & (1usize << 53), 0); // AArch64 PXN
    assert_ne!(entry & (1usize << 54), 0); // AArch64 UXN
    assert_eq!((entry >> 6) & 0b11, 0); // AP: privileged read/write
    assert_eq!(entry & (1usize << 11), 0); // nG: global kernel mapping
}

#[test]
fn writable_executable_mapping_is_rejected_without_allocating_tables() {
    let fixture = Fixture::new([FrameState::Free; 8]);
    let mut mapper = unsafe { PageMapper::<_>::create(&fixture.allocator) }.unwrap();
    let before = fixture.allocator.frame_stats().unwrap();
    assert!(mapper
        .map_range(
            VirtualAddress::new(0x8000),
            fixture.base(),
            PAGE_SIZE,
            MemAttribute {
                flags: MemFlags::READ | MemFlags::WRITE | MemFlags::EXECUTE,
                memory_type: MemType::Normal(CachePolicy::WriteBack),
            },
        )
        .is_err());
    assert_eq!(mapper.translate(0x8000), None);
    assert_eq!(fixture.allocator.frame_stats().unwrap(), before);
}

#[test]
fn retained_kernel_table_is_not_reclaimed_on_mapper_drop() {
    let fixture = Fixture::new([FrameState::Free; 2]);
    let allocator = &fixture.allocator;
    let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
    let root = mapper.root_address();
    mapper.retain_tables();
    drop(mapper);
    assert_eq!(allocator.usage().unwrap().free(), 1);
    // No hardware used this test root; explicitly return its transferred owner.
    unsafe {
        allocator.free_frame(root).unwrap();
    }
    assert_eq!(allocator.usage().unwrap().free(), 2);
}

#[test]
fn frame_concurrent_allocations_remain_exclusive_across_yields() {
    use crate::{scheduler, types::Arc};
    use core::sync::atomic::{AtomicUsize, Ordering};
    let done = Arc::new(AtomicUsize::new(0));
    for worker in 0..4 {
        let done = done.clone();
        crate::thread::spawn(move || {
            let allocator = FirstFitFrameAllocator::instance();
            for iteration in 0..32 {
                let run = allocator.alloc_owned_frames(2).unwrap();
                let bytes = kernel_phys_to_virt(run.address()).into_raw() as *mut u8;
                let pattern = (worker * 32 + iteration) as u8;
                unsafe {
                    bytes.write_bytes(pattern, 2 * PAGE_SIZE);
                }
                scheduler::yield_me();
                let contents = unsafe { core::slice::from_raw_parts(bytes, 2 * PAGE_SIZE) };
                assert!(contents.iter().all(|b| *b == pattern));
            }
            done.fetch_add(1, Ordering::Release);
        })
        .expect("spawn frame allocator test worker");
    }
    while done.load(Ordering::Acquire) != 4 {
        scheduler::yield_me();
    }
}

#[test]
fn carve_ram_holes_excludes_reserved_and_aligns() {
    use crate::mm::memory_bank::carve_ram_holes;
    let region = |base: usize, size: usize, reserved: bool| MemoryRegion {
        base: PhysicalAddress::new(base),
        size,
        is_reserved: reserved,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        name: "test",
    };
    let ram = region(0x1000_0000, 0x4_0000, false);
    let reserved = [
        region(0x1001_0000, 0x1_0000, true),
        region(0x1002_0000, 0x1_0000, true),
    ];
    let holes = carve_ram_holes(&ram, reserved.iter()).unwrap();
    assert_eq!(
        holes.as_slice(),
        [
            (PhysicalAddress::new(0x1000_0000), 0x1_0000),
            (PhysicalAddress::new(0x1003_0000), 0x1_0000),
        ]
    );
}

#[test]
fn carve_ram_holes_rejects_non_page_aligned() {
    use crate::mm::memory_bank::carve_ram_holes;
    let region = |base: usize, size: usize, reserved: bool| MemoryRegion {
        base: PhysicalAddress::new(base),
        size,
        is_reserved: reserved,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        name: "test",
    };
    let ram = region(0x2000_0000, 4 * PAGE_SIZE, false);
    let misaligned_base = [region(0x2000_1001, 2 * PAGE_SIZE, true)];
    assert!(carve_ram_holes(&ram, misaligned_base.iter()).is_err());
    let misaligned_end = [region(0x2000_2000, PAGE_SIZE + 1, true)];
    assert!(carve_ram_holes(&ram, misaligned_end.iter()).is_err());
    let aligned = [region(0x2000_2000, PAGE_SIZE, true)];
    assert!(carve_ram_holes(&ram, aligned.iter()).is_ok());
}

#[test]
fn carve_ram_holes_full_overlap() {
    use crate::mm::memory_bank::carve_ram_holes;
    let region = |base: usize, size: usize, reserved: bool| MemoryRegion {
        base: PhysicalAddress::new(base),
        size,
        is_reserved: reserved,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        name: "test",
    };
    let ram = region(0x4000_0000, 2 * PAGE_SIZE, false);
    let reserved = [region(0x4000_0000, 2 * PAGE_SIZE, true)];
    let holes = carve_ram_holes(&ram, reserved.iter()).unwrap();
    assert_eq!(holes.as_slice(), []);
}

#[test]
fn carve_ram_holes_partial_prefix() {
    use crate::mm::memory_bank::carve_ram_holes;
    let region = |base: usize, size: usize, reserved: bool| MemoryRegion {
        base: PhysicalAddress::new(base),
        size,
        is_reserved: reserved,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        name: "test",
    };
    let ram = region(0x5000_0000, 3 * PAGE_SIZE, false);
    let reserved = [region(0x5000_0000, PAGE_SIZE, true)];
    let holes = carve_ram_holes(&ram, reserved.iter()).unwrap();
    assert_eq!(
        holes.as_slice(),
        [(PhysicalAddress::new(0x5000_1000), 2 * PAGE_SIZE)]
    );
}

#[test]
fn carve_ram_holes_multiple_reserved() {
    use crate::mm::memory_bank::carve_ram_holes;
    let region = |base: usize, size: usize, reserved: bool| MemoryRegion {
        base: PhysicalAddress::new(base),
        size,
        is_reserved: reserved,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        name: "test",
    };
    let ram = region(0x6000_0000, 5 * PAGE_SIZE, false);
    let reserved = [
        region(0x6000_1000, PAGE_SIZE, true),
        region(0x6000_3000, PAGE_SIZE, true),
    ];
    let holes = carve_ram_holes(&ram, reserved.iter()).unwrap();
    assert_eq!(
        holes.as_slice(),
        [
            (PhysicalAddress::new(0x6000_0000), PAGE_SIZE),
            (PhysicalAddress::new(0x6000_2000), PAGE_SIZE),
            (PhysicalAddress::new(0x6000_4000), PAGE_SIZE),
        ]
    );
}

#[test]
fn owned_virtual_range_uses_scattered_frames_and_reclaims_tables() {
    use FrameState::{Free as F, Reserved as R};
    let count = crate::arch::page::PageEntry::LEVELS as usize + 3;
    let mut states = [R; 14];
    for i in 0..count {
        states[2 * i] = F;
    }
    let fixture = Fixture::new(states);
    let allocator = &fixture.allocator;
    let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
    let before = allocator.frame_stats().unwrap();
    let va = VirtualAddress::new(0x1000);
    unsafe { mapper.map_owned_range(va, 3 * PAGE_SIZE) }.unwrap();
    let mut previous = None;
    for index in 0..3 {
        let physical = mapper.translate(va.into_raw() + index * PAGE_SIZE).unwrap();
        if let Some(last) = previous {
            assert_eq!(physical.into_raw(), last + 2 * PAGE_SIZE);
        }
        previous = Some(physical.into_raw());
        let ptr = kernel_phys_to_virt(physical).into_raw() as *mut u8;
        unsafe { ptr.write_bytes(index as u8, PAGE_SIZE) };
    }
    assert_eq!(allocator.frame_stats().unwrap().free, 0);
    unsafe { mapper.release_owned_range(va, 3 * PAGE_SIZE) };
    assert!(mapper.translate(va.into_raw()).is_none());
    let after = allocator.frame_stats().unwrap();
    assert_eq!(
        (after.free, after.allocated),
        (before.free, before.allocated)
    );
    drop(mapper);
    assert_eq!(allocator.frame_stats().unwrap().free, count);
}

#[test]
fn owned_mapping_oom_rolls_back_partial_tables_and_backing() {
    for free in 1..crate::arch::page::PageEntry::LEVELS as usize + 3 {
        let mut states = [FrameState::Reserved; 8];
        states[..free].fill(FrameState::Free);
        let fixture = Fixture::new(states);
        let allocator = &fixture.allocator;
        let mut mapper = unsafe { PageMapper::<_>::create(allocator) }.unwrap();
        let before = allocator.frame_stats().unwrap();
        let va = VirtualAddress::new(0x1000);
        assert!(unsafe { mapper.map_owned_range(va, 3 * PAGE_SIZE) }.is_err());
        assert!(mapper.translate(va.into_raw()).is_none());
        let after = allocator.frame_stats().unwrap();
        assert_eq!(
            (after.free, after.allocated),
            (before.free, before.allocated)
        );
        drop(mapper);
        assert_eq!(allocator.frame_stats().unwrap().free, free);
    }
}
