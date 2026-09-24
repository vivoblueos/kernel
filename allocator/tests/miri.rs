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

use allocator_crate::{
    llff::Heap as LlffHeap,
    slab::{Slab, SlabHeap},
    tlsf::Tlsf,
};
use core::{
    alloc::Layout,
    mem::MaybeUninit,
    ptr::{addr_of_mut, NonNull},
};

const SMALL_ARENA_SIZE: usize = 16 * 1024;
const LARGE_ARENA_SIZE: usize = 128 * 1024;

#[repr(align(4096))]
struct Arena<const N: usize>([MaybeUninit<u8>; N]);

struct LiveAllocation {
    ptr: NonNull<u8>,
    layout: Layout,
    tag: u8,
}

struct XorShift32(u32);

impl XorShift32 {
    const fn new(seed: u32) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u32 {
        let mut value = self.0;
        value ^= value << 13;
        value ^= value >> 17;
        value ^= value << 5;
        self.0 = value;
        value
    }

    fn range(&mut self, start: usize, end: usize) -> usize {
        start + self.next() as usize % (end - start)
    }
}

fn layout(size: usize, align: usize) -> Layout {
    Layout::from_size_align(size, align).unwrap()
}

unsafe fn fill(allocation: &LiveAllocation) {
    allocation
        .ptr
        .as_ptr()
        .write_bytes(allocation.tag, allocation.layout.size());
}

unsafe fn verify(allocation: &LiveAllocation) {
    for offset in 0..allocation.layout.size() {
        assert_eq!(
            allocation.ptr.as_ptr().add(offset).read(),
            allocation.tag,
            "allocation payload changed at byte {offset}"
        );
    }
}

fn verify_live_allocations(live: &[LiveAllocation]) {
    for allocation in live {
        assert_eq!(
            allocation.ptr.as_ptr().addr() % allocation.layout.align(),
            0
        );
        unsafe { verify(allocation) };
    }
    for (index, left) in live.iter().enumerate() {
        let left_range = left.ptr.as_ptr().addr()..left.ptr.as_ptr().addr() + left.layout.size();
        for right in &live[index + 1..] {
            let right_range =
                right.ptr.as_ptr().addr()..right.ptr.as_ptr().addr() + right.layout.size();
            assert!(
                left_range.end <= right_range.start || right_range.end <= left_range.start,
                "live allocations overlap"
            );
        }
    }
}

unsafe fn static_arena<const N: usize>(arena: *mut Arena<N>) -> &'static mut [MaybeUninit<u8>] {
    core::slice::from_raw_parts_mut((*arena).0.as_mut_ptr(), N)
}

#[test]
fn tlsf_allocate_reallocate_and_coalesce() {
    let mut arena = [MaybeUninit::uninit(); SMALL_ARENA_SIZE];
    let mut heap: Tlsf<'_, u32, u32, 16, 16> = Tlsf::new();
    heap.insert_free_block(&mut arena);
    let initial_largest = heap.get_max_free_block_size();

    let old_layout = layout(31, 64);
    let pointer = heap.allocate(&old_layout).expect("TLSF allocation failed");
    let mut allocation = LiveAllocation {
        ptr: pointer,
        layout: old_layout,
        tag: 0x5a,
    };
    unsafe { fill(&allocation) };

    let new_layout = layout(257, 64);
    let new_pointer =
        unsafe { heap.reallocate(pointer, &new_layout) }.expect("TLSF reallocation failed");
    for offset in 0..old_layout.size() {
        assert_eq!(unsafe { new_pointer.as_ptr().add(offset).read() }, 0x5a);
    }
    allocation.ptr = new_pointer;
    allocation.layout = new_layout;
    unsafe { fill(&allocation) };
    verify_live_allocations(core::slice::from_ref(&allocation));

    unsafe { heap.deallocate(new_pointer, new_layout.align()) };
    assert_eq!(heap.allocated(), 0);
    assert_eq!(heap.get_max_free_block_size(), initial_largest);
}

#[test]
fn tlsf_deterministic_stress() {
    for seed in [0xc0ff_ee11, 0xdead_beef] {
        let mut arena = [MaybeUninit::uninit(); SMALL_ARENA_SIZE];
        let mut heap: Tlsf<'_, u32, u32, 16, 16> = Tlsf::new();
        heap.insert_free_block(&mut arena);
        let mut rng = XorShift32::new(seed);
        let mut live = Vec::new();

        for step in 0..40 {
            if live.is_empty() || rng.range(0, 100) < 60 {
                let requested = rng.range(1, 513);
                let align = 1usize << rng.range(0, 7);
                let requested_layout = layout(requested, align);
                if let Some(ptr) = heap.allocate(&requested_layout) {
                    let allocation = LiveAllocation {
                        ptr,
                        layout: requested_layout,
                        tag: (step as u8).wrapping_add(1),
                    };
                    unsafe { fill(&allocation) };
                    live.push(allocation);
                }
            } else {
                let index = rng.range(0, live.len());
                let allocation = live.swap_remove(index);
                unsafe {
                    verify(&allocation);
                    heap.deallocate(allocation.ptr, allocation.layout.align());
                }
            }
            verify_live_allocations(&live);
        }

        for allocation in live.drain(..) {
            unsafe {
                verify(&allocation);
                heap.deallocate(allocation.ptr, allocation.layout.align());
            }
        }
        assert_eq!(heap.allocated(), 0);
    }
}

#[test]
fn llff_allocate_reallocate_and_coalesce() {
    static mut ARENA: Arena<SMALL_ARENA_SIZE> =
        Arena([const { MaybeUninit::uninit() }; SMALL_ARENA_SIZE]);
    let arena = unsafe { static_arena(addr_of_mut!(ARENA)) };
    let mut heap = LlffHeap::from_slice(arena);
    let initial_largest = heap.get_max_free_block_size();

    let old_layout = layout(31, 8);
    let pointer = heap
        .allocate_first_fit(&old_layout)
        .expect("LLFF allocation failed");
    let allocation = LiveAllocation {
        ptr: pointer,
        layout: old_layout,
        tag: 0xa5,
    };
    unsafe { fill(&allocation) };

    let new_size = 257;
    let new_pointer =
        unsafe { heap.realloc(pointer, &old_layout, new_size) }.expect("LLFF reallocation failed");
    for offset in 0..old_layout.size() {
        assert_eq!(unsafe { new_pointer.as_ptr().add(offset).read() }, 0xa5);
    }
    unsafe { heap.deallocate(new_pointer, &layout(new_size, old_layout.align())) };
    assert_eq!(heap.allocated(), 0);
    assert_eq!(heap.get_max_free_block_size(), initial_largest);
}

#[test]
fn llff_deterministic_stress() {
    static mut ARENA: Arena<LARGE_ARENA_SIZE> =
        Arena([const { MaybeUninit::uninit() }; LARGE_ARENA_SIZE]);
    let arena = unsafe { static_arena(addr_of_mut!(ARENA)) };
    let mut heap = LlffHeap::from_slice(arena);
    let mut rng = XorShift32::new(0x3141_5926);
    let mut live = Vec::new();

    for step in 0..48 {
        if live.is_empty() || rng.range(0, 100) < 60 {
            let requested = rng.range(1, 513);
            let align = 1usize << rng.range(0, 7);
            let requested_layout = layout(requested, align);
            if let Some(ptr) = heap.allocate_first_fit(&requested_layout) {
                let allocation = LiveAllocation {
                    ptr,
                    layout: requested_layout,
                    tag: (step as u8).wrapping_add(1),
                };
                unsafe { fill(&allocation) };
                live.push(allocation);
            }
        } else {
            let index = rng.range(0, live.len());
            let allocation = live.swap_remove(index);
            unsafe {
                verify(&allocation);
                heap.deallocate(allocation.ptr, &allocation.layout);
            }
        }
        verify_live_allocations(&live);
    }

    for allocation in live.drain(..) {
        unsafe {
            verify(&allocation);
            heap.deallocate(allocation.ptr, &allocation.layout);
        }
    }
    assert_eq!(heap.allocated(), 0);
}

#[test]
fn slab_exhaustion_and_reuse() {
    const BLOCK_SIZE: usize = 64;
    const BLOCK_COUNT: usize = 8;
    let mut arena = Arena([MaybeUninit::uninit(); BLOCK_SIZE * BLOCK_COUNT]);
    let arena = &mut arena.0[..];
    let mut slab = Slab::new();
    unsafe {
        slab.init(
            arena.as_mut_ptr().expose_provenance(),
            BLOCK_COUNT,
            BLOCK_SIZE,
        )
    };

    let requested_layout = layout(37, 8);
    let mut pointers = Vec::new();
    for tag in 1..=BLOCK_COUNT {
        let pointer = slab
            .allocate(&requested_layout)
            .expect("slab allocation failed");
        let allocation = LiveAllocation {
            ptr: pointer,
            layout: requested_layout,
            tag: tag as u8,
        };
        unsafe { fill(&allocation) };
        pointers.push(allocation);
    }
    assert!(slab.allocate(&requested_layout).is_none());
    verify_live_allocations(&pointers);

    for allocation in pointers {
        unsafe { slab.deallocate(allocation.ptr) };
    }
    let pointer = slab
        .allocate(&requested_layout)
        .expect("slab was not reusable");
    unsafe { slab.deallocate(pointer) };
}

#[test]
#[should_panic(expected = "Double free detected")]
fn slab_detects_double_free() {
    const BLOCK_SIZE: usize = 64;
    let mut arena = Arena([MaybeUninit::uninit(); BLOCK_SIZE]);
    let arena = &mut arena.0[..];
    let mut slab = Slab::new();
    unsafe { slab.init(arena.as_mut_ptr().expose_provenance(), 1, BLOCK_SIZE) };
    let pointer = slab.allocate(&layout(16, 8)).unwrap();
    unsafe {
        slab.deallocate(pointer);
        slab.deallocate(pointer);
    }
}

#[test]
fn slab_heap_cross_class_reallocate() {
    type TestHeap = SlabHeap<1, 1, 1, 1, 1, 1, 1, 1, 1, 1>;
    let mut arena = Arena([MaybeUninit::uninit(); LARGE_ARENA_SIZE]);
    let arena = &mut arena.0[..];
    let mut heap = TestHeap::new();
    unsafe { heap.init(arena.as_mut_ptr().expose_provenance(), arena.len()) };

    let old_layout = layout(31, 8);
    let pointer = heap
        .allocate(&old_layout)
        .expect("SlabHeap allocation failed");
    let allocation = LiveAllocation {
        ptr: pointer,
        layout: old_layout,
        tag: 0x3c,
    };
    unsafe { fill(&allocation) };

    let new_layout = layout(1537, 64);
    let new_pointer =
        unsafe { heap.reallocate(pointer, &new_layout) }.expect("SlabHeap reallocation failed");
    for offset in 0..old_layout.size() {
        assert_eq!(unsafe { new_pointer.as_ptr().add(offset).read() }, 0x3c);
    }
    unsafe { heap.deallocate(new_pointer, &new_layout) };
    assert_eq!(heap.allocated(), 0);
}

#[cfg(allocator = "slab_dynamic")]
#[test]
fn dynamic_slab_heap_small_and_system_allocations() {
    use allocator_crate::slab::DynamicSlabHeap;

    let mut arena = Arena([MaybeUninit::uninit(); 256 * 1024]);
    let arena = &mut arena.0[..];
    let mut heap = DynamicSlabHeap::new();
    unsafe { heap.init(arena.as_mut_ptr().expose_provenance(), arena.len()) };

    let small_layout = layout(63, 16);
    let small = heap
        .allocate(&small_layout)
        .expect("dynamic slab allocation failed");
    let large_layout = layout(2049, 64);
    let large = heap
        .allocate(&large_layout)
        .expect("dynamic system allocation failed");
    let live = [
        LiveAllocation {
            ptr: small,
            layout: small_layout,
            tag: 0x11,
        },
        LiveAllocation {
            ptr: large,
            layout: large_layout,
            tag: 0x22,
        },
    ];
    for allocation in &live {
        unsafe { fill(allocation) };
    }
    verify_live_allocations(&live);

    unsafe {
        heap.deallocate(small, &small_layout);
        heap.deallocate(large, &large_layout);
    }
    assert_eq!(heap.allocated(), 0);
}
