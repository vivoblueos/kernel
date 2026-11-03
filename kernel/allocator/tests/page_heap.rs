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

#[path = "page_heap_support.rs"]
mod support;
use allocator_crate::page_heap::*;
use std::alloc::Layout;
use support::Fixture;

#[test]
fn large_run_keeps_all_actual_pages_and_rejects_interior_free() {
    let mut f = Fixture::new(16);
    let span = f.take(4, 4 * PAGE_SIZE).unwrap();
    let layout = Layout::from_size_align(2 * PAGE_SIZE + 1, 4 * PAGE_SIZE).unwrap();
    let allocation = unsafe { f.heap.commit_large(span, layout) }.unwrap();
    assert_eq!(allocation.ptr, span.start());
    assert_eq!(allocation.capacity, 4 * PAGE_SIZE);
    let info = f.heap.allocation_info(allocation.ptr).unwrap();
    assert_eq!(info.kind, AllocationKind::Large);
    assert_eq!(info.requested_size, Some(layout.size()));
    assert_eq!(info.align, layout.align());
    assert_eq!(info.span, span);
    let interior = f
        .window
        .span(f.window.index_of(span.start()).unwrap() + 1, 1)
        .unwrap();
    assert_eq!(
        unsafe { f.heap.free(interior.start(), None) },
        Err(HeapError::InteriorPointer)
    );
    let within_head = unsafe { std::ptr::NonNull::new_unchecked(allocation.ptr.as_ptr().add(1)) };
    assert_eq!(
        unsafe { f.heap.free(within_head, None) },
        Err(HeapError::InteriorPointer)
    );
    assert_eq!(
        f.heap.stats(),
        HeapStats {
            large_pages: 4,
            backing_bytes: 16384,
            live_objects: 1,
            charged_bytes: 16384,
            peak_charged_bytes: 16384,
            ..HeapStats::default()
        }
    );
    match unsafe { f.heap.free(allocation.ptr, Some(layout)) }.unwrap() {
        ReleaseAction::Pages(detached) => f.release(detached),
        ReleaseAction::None => panic!("large allocation must release its run"),
    }
    assert_eq!(f.free_pages(), 16);
    assert_eq!(f.heap.stats().backing_bytes, 0);
    assert_eq!(f.heap.stats().peak_charged_bytes, 16384);
    assert_eq!(
        unsafe { f.heap.free(allocation.ptr, None) },
        Err(HeapError::NotAllocated)
    );
}

#[test]
fn classification_respects_alignment_and_rounds_page_requests() {
    for (size, align, capacity) in [
        (1, 1, 8),
        (8, 1, 8),
        (9, 8, 16),
        (17, 32, 32),
        (31, 64, 64),
        (65, 128, 128),
        (129, 256, 256),
        (257, 512, 512),
        (513, 1024, 1024),
        (1024, 8, 1024),
    ] {
        let AllocationPlan::Slab(class) =
            classify(Layout::from_size_align(size, align).unwrap()).unwrap()
        else {
            panic!("small request should use a slab");
        };
        assert_eq!(class.size(), capacity);
    }
    for (size, align, pages, page_align) in [
        (1025, 1, 1, 4096),
        (1, 2048, 1, 4096),
        (4097, 64, 2, 4096),
        (8193, 16384, 3, 16384),
    ] {
        assert_eq!(
            classify(Layout::from_size_align(size, align).unwrap()),
            Ok(AllocationPlan::Pages(PageRequest {
                pages,
                align: page_align
            }))
        );
    }
    assert_eq!(
        classify(Layout::from_size_align(0, 8).unwrap()),
        Err(HeapError::InvalidRequest)
    );
}

#[test]
fn geometry_rejects_invalid_bounds_and_accepts_object_addresses() {
    let f = Fixture::new(4);
    let base = f.window.base();
    let unaligned = unsafe { std::ptr::NonNull::new_unchecked(base.as_ptr().add(1)) };
    assert!(matches!(
        unsafe { PageWindow::new(unaligned, 1) },
        Err(HeapError::InvalidGeometry)
    ));
    assert!(matches!(
        unsafe { PageWindow::new(base, 0) },
        Err(HeapError::InvalidGeometry)
    ));
    assert!(matches!(
        unsafe { PageWindow::new(base, usize::MAX) },
        Err(HeapError::InvalidGeometry)
    ));
    assert!(matches!(
        unsafe { PageSpan::new(base, 0) },
        Err(HeapError::InvalidGeometry)
    ));
    assert!(matches!(
        unsafe { PageSpan::new(base, usize::MAX) },
        Err(HeapError::InvalidGeometry)
    ));
    assert_eq!(f.window.index_of(unaligned), Ok(0));
    assert_eq!(f.window.span(3, 2), Err(HeapError::OutOfWindow));
    assert_eq!(f.window.span(usize::MAX, 1), Err(HeapError::OutOfWindow));
    assert!(matches!(
        f.window.span(0, 0),
        Err(HeapError::InvalidGeometry)
    ));
    let end = unsafe { std::ptr::NonNull::new_unchecked(base.as_ptr().add(4 * PAGE_SIZE)) };
    assert_eq!(f.window.index_of(end), Err(HeapError::OutOfWindow));
    assert_eq!(f.heap.largest_free_slot(), 0);
    assert_eq!(f.heap.stats(), HeapStats::default());
    let empty = unsafe { PageHeap::new(f.window) }.unwrap();
    assert_eq!(empty.stats(), HeapStats::default());
}

#[test]
fn invalid_large_commits_and_layouts_preserve_existing_allocation() {
    let mut f = Fixture::new(8);
    let span = f.take(2, PAGE_SIZE).unwrap();
    let layout = Layout::from_size_align(4097, 8).unwrap();
    let a = unsafe { f.heap.commit_large(span, layout) }.unwrap();
    let stats = f.heap.stats();
    assert_eq!(
        unsafe { f.heap.commit_large(span, layout) },
        Err(HeapError::Conflict)
    );
    let outside = unsafe { PageSpan::new(f.window.span(7, 1).unwrap().start(), 2) }.unwrap();
    assert_eq!(
        unsafe { f.heap.commit_large(outside, layout) },
        Err(HeapError::OutOfWindow)
    );
    let candidate = f.take(1, PAGE_SIZE).unwrap();
    let too_big = Layout::from_size_align(4097, 1).unwrap();
    assert_eq!(
        unsafe { f.heap.commit_large(candidate, too_big) },
        Err(HeapError::InvalidRequest)
    );
    let too_aligned = Layout::from_size_align(2048, 65536).unwrap();
    assert_eq!(
        unsafe { f.heap.commit_large(candidate, too_aligned) },
        Err(HeapError::InvalidRequest)
    );
    let zero = Layout::from_size_align(0, 1).unwrap();
    assert_eq!(
        unsafe { f.heap.commit_large(candidate, zero) },
        Err(HeapError::InvalidRequest)
    );
    let unaligned = unsafe { std::ptr::NonNull::new_unchecked(candidate.start().as_ptr().add(1)) };
    let unaligned_span = unsafe { PageSpan::new(unaligned, 1) };
    if let Ok(unaligned_span) = unaligned_span {
        assert_eq!(
            unsafe {
                f.heap
                    .commit_large(unaligned_span, Layout::from_size_align(2048, 1).unwrap())
            },
            Err(HeapError::InvalidGeometry)
        );
    } else {
        assert_eq!(unaligned_span, Err(HeapError::InvalidGeometry));
    }
    assert_eq!(
        unsafe {
            f.heap
                .free(a.ptr, Some(Layout::from_size_align(4098, 8).unwrap()))
        },
        Err(HeapError::LayoutMismatch)
    );
    assert_eq!(
        unsafe {
            f.heap
                .free(a.ptr, Some(Layout::from_size_align(4097, 16).unwrap()))
        },
        Err(HeapError::LayoutMismatch)
    );
    assert_eq!(
        unsafe { f.heap.free(candidate.start(), None) },
        Err(HeapError::NotAllocated)
    );
    assert_eq!(
        f.heap.allocation_info(candidate.start()).unwrap_err(),
        HeapError::NotAllocated
    );
    let other = Fixture::new(1);
    assert_eq!(
        unsafe { f.heap.free(other.window.base(), None) },
        Err(HeapError::NotAllocated)
    );
    assert_eq!(f.heap.stats(), stats);
    let info = f.heap.allocation_info(a.ptr).unwrap();
    assert_eq!(info.requested_size, Some(4097));
    assert_eq!(info.capacity, 8192);
    assert_eq!(info.align, 8);
    assert_eq!(info.span, span);
    f.release(candidate);
    match unsafe { f.heap.free(a.ptr, None) }.unwrap() {
        ReleaseAction::Pages(detached) => f.release(detached),
        ReleaseAction::None => panic!("large allocation must release its run"),
    }
    assert_eq!(f.free_pages(), 8);
}

#[test]
fn slab_rechecks_existing_capacity_and_returns_last_page() {
    let mut f = Fixture::new(8);
    let class = match classify(Layout::from_size_align(33, 16).unwrap()).unwrap() {
        AllocationPlan::Slab(class) => class,
        AllocationPlan::Pages(_) => panic!("64-byte class required"),
    };
    let first = f.take(1, PAGE_SIZE).unwrap();
    let extra = f.take(1, PAGE_SIZE).unwrap();
    unsafe {
        PageHeap::format_slab(first, class).unwrap();
    }
    unsafe {
        PageHeap::format_slab(extra, class).unwrap();
    }
    let a = match unsafe { f.heap.commit_slab(first, class) }.unwrap() {
        SlabCommit::Inserted(a) => a,
        SlabCommit::Existing(_) => panic!("first page must be inserted"),
    };
    let b = match unsafe { f.heap.commit_slab(extra, class) }.unwrap() {
        SlabCommit::Existing(b) => b,
        SlabCommit::Inserted(_) => panic!("existing page has capacity"),
    };
    f.release(extra);
    assert_ne!(a.ptr, b.ptr);
    assert_eq!(f.heap.stats().slab_pages, 1);
    assert_eq!(
        unsafe { f.heap.free(a.ptr, None) }.unwrap(),
        ReleaseAction::None
    );
    assert_eq!(
        unsafe { f.heap.free(a.ptr, None) },
        Err(HeapError::NotAllocated)
    );
    match unsafe { f.heap.free(b.ptr, None) }.unwrap() {
        ReleaseAction::Pages(span) => f.release(span),
        ReleaseAction::None => panic!("last object must detach its page"),
    }
    assert_eq!(f.free_pages(), 8);
    assert_eq!(f.heap.stats().live_objects, 0);
}

// Catches partial owner/stat publication or payload damage on rejected runs.
// Every candidate is backed by a real arena, including the out-of-window case.
#[test]
fn rejected_publication_preserves_live_data_and_allows_candidate_reuse() {
    let mut f = Fixture::new(8);
    let mut outside = Fixture::new(2);
    let layout = Layout::from_size_align(4097, 8).unwrap();
    let span = f.take(2, PAGE_SIZE).unwrap();
    let live = unsafe { f.heap.commit_large(span, layout) }.unwrap();
    unsafe { live.ptr.as_ptr().write_bytes(0x7b, layout.size()) };
    let before = f.heap.stats();
    let candidate = f.take(2, PAGE_SIZE).unwrap();
    let foreign = outside.take(2, PAGE_SIZE).unwrap();
    for (rejected, request, error) in [
        (span, layout, HeapError::Conflict),
        (foreign, layout, HeapError::OutOfWindow),
        (
            candidate,
            Layout::from_size_align(8193, 8).unwrap(),
            HeapError::InvalidRequest,
        ),
    ] {
        assert_eq!(
            unsafe { f.heap.commit_large(rejected, request) },
            Err(error)
        );
        assert_eq!(f.heap.stats(), before);
        assert_eq!(f.free_pages(), 4);
        let info = f.heap.allocation_info(live.ptr).unwrap();
        assert_eq!(info.kind, AllocationKind::Large);
        assert_eq!(info.span, span);
        assert_eq!(info.requested_size, Some(4097));
        assert_eq!(info.capacity, 8192);
        assert_eq!(info.align, 8);
        for offset in 0..layout.size() {
            assert_eq!(unsafe { live.ptr.as_ptr().add(offset).read() }, 0x7b);
        }
        assert_eq!(
            f.heap.allocation_info(candidate.start()).unwrap_err(),
            HeapError::NotAllocated
        );
    }
    // The raw core leaves rejected runs with the caller, which returns them.
    outside.release(foreign);
    f.release(candidate);
    assert_eq!(outside.free_pages(), 2);
    assert_eq!(f.free_pages(), 6);
    let reused = f.take(2, PAGE_SIZE).unwrap();
    assert_eq!(reused, candidate);
    let retry = unsafe { f.heap.commit_large(reused, layout) }.unwrap();
    assert_eq!(f.heap.stats().live_objects, 2);
    for allocation in [retry, live] {
        let ReleaseAction::Pages(run) =
            (unsafe { f.heap.free(allocation.ptr, Some(layout)) }).unwrap()
        else {
            panic!("large allocation must return every page");
        };
        f.release(run);
    }
    assert_eq!(f.free_pages(), 8);
    assert_eq!(f.heap.stats().backing_bytes, 0);
    assert_eq!(f.heap.stats().live_objects, 0);
}

#[test]
fn all_slab_classes_preserve_payloads_and_reclaim_full_pages() {
    for size in CLASS_SIZES {
        let mut f = Fixture::new(4);
        let layout = Layout::from_size_align(size, size).unwrap();
        let AllocationPlan::Slab(class) = classify(layout).unwrap() else {
            unreachable!()
        };
        let first = f.take(1, PAGE_SIZE).unwrap();
        unsafe {
            PageHeap::format_slab(first, class).unwrap();
        }
        let SlabCommit::Inserted(a) = (unsafe { f.heap.commit_slab(first, class) }).unwrap() else {
            panic!()
        };
        let mut objects = vec![a];
        while let Some(a) = f.heap.try_alloc_small(class).unwrap() {
            objects.push(a);
        }
        assert_eq!(f.heap.largest_free_slot(), 0);
        let first_count = objects.len();
        let second = f.take(1, PAGE_SIZE).unwrap();
        unsafe {
            PageHeap::format_slab(second, class).unwrap();
        }
        let SlabCommit::Inserted(a) = (unsafe { f.heap.commit_slab(second, class) }).unwrap()
        else {
            panic!()
        };
        objects.push(a);
        for (i, object) in objects.iter().enumerate() {
            assert_eq!(object.ptr.as_ptr().addr() % size, 0);
            assert!(
                object.ptr.as_ptr().addr()
                    >= if i < first_count {
                        first.start().as_ptr().addr()
                    } else {
                        second.start().as_ptr().addr()
                    } + size
            );
            unsafe {
                std::ptr::write_bytes(object.ptr.as_ptr(), (i % 251) as u8, size);
            }
        }
        let mut addresses: Vec<_> = objects
            .iter()
            .map(|object| object.ptr.as_ptr().addr())
            .collect();
        addresses.sort_unstable();
        assert!(addresses.windows(2).all(|pair| pair[1] - pair[0] >= size));
        for (i, object) in objects.iter().enumerate() {
            for j in 0..size {
                assert_eq!(unsafe { *object.ptr.as_ptr().add(j) }, (i % 251) as u8);
            }
            let info = f.heap.allocation_info(object.ptr).unwrap();
            assert_eq!(info.kind, AllocationKind::Slab(class));
            assert_eq!(info.capacity, size);
        }
        let first_object = objects[0];
        assert_eq!(
            unsafe { f.heap.free(first_object.ptr, Some(layout)) }.unwrap(),
            ReleaseAction::None
        );
        assert_eq!(f.heap.largest_free_slot(), size);
        let reused = f.heap.try_alloc_small(class).unwrap().unwrap();
        assert_eq!(reused.ptr, first_object.ptr);
        for object in objects
            .iter()
            .step_by(2)
            .chain(objects.iter().skip(1).step_by(2))
        {
            if let ReleaseAction::Pages(span) =
                unsafe { f.heap.free(object.ptr, Some(layout)) }.unwrap()
            {
                f.release(span);
            }
        }
        assert_eq!(f.free_pages(), 4);
        assert_eq!(f.heap.stats().slab_pages, 0);
        assert_eq!(f.heap.stats().charged_bytes, 0);
    }
}

#[test]
fn slab_rejects_two_page_candidates_without_consuming_them() {
    let mut f = Fixture::new(4);
    let AllocationPlan::Slab(class) = classify(Layout::from_size_align(8, 8).unwrap()).unwrap()
    else {
        unreachable!()
    };
    let span = f.take(2, PAGE_SIZE).unwrap();
    assert_eq!(
        unsafe { PageHeap::format_slab(span, class) },
        Err(HeapError::InvalidRequest)
    );
    assert_eq!(
        unsafe { f.heap.commit_slab(span, class) },
        Err(HeapError::InvalidRequest)
    );
    f.release(span);
    assert_eq!(f.free_pages(), 4);
}

#[test]
fn reuse_preserves_capacity_and_rejects_invalid_requests() {
    let mut f = Fixture::new(8);
    let span = f.take(4, PAGE_SIZE).unwrap();
    let old = Layout::from_size_align(9000, 64).unwrap();
    let a = unsafe { f.heap.commit_large(span, old) }.unwrap();
    let stats = f.heap.stats();
    let small = Layout::from_size_align(1000, 64).unwrap();
    assert_eq!(
        unsafe { f.heap.try_reuse(a.ptr, Some(old), small) },
        Ok(true)
    );
    let info = f.heap.allocation_info(a.ptr).unwrap();
    assert_eq!(info.requested_size, Some(1000));
    assert_eq!(info.span.pages(), 4);
    assert_eq!(f.heap.stats(), stats);
    assert_eq!(
        unsafe { f.heap.try_reuse(a.ptr, Some(old), small) },
        Err(HeapError::LayoutMismatch)
    );
    assert_eq!(
        unsafe {
            f.heap.try_reuse(
                a.ptr,
                Some(small),
                Layout::from_size_align(20000, 64).unwrap(),
            )
        },
        Ok(false)
    );
    assert_eq!(
        f.heap.allocation_info(a.ptr).unwrap().requested_size,
        Some(1000)
    );
    match unsafe { f.heap.free(a.ptr, Some(small)) }.unwrap() {
        ReleaseAction::Pages(span) => f.release(span),
        ReleaseAction::None => panic!(),
    }
    assert_eq!(f.free_pages(), 8);
}

#[test]
fn slab_reuse_and_invalid_free_leave_allocation_unchanged() {
    let mut f = Fixture::new(4);
    let old = Layout::from_size_align(33, 16).unwrap();
    let AllocationPlan::Slab(class) = classify(old).unwrap() else {
        panic!()
    };
    let span = f.take(1, PAGE_SIZE).unwrap();
    unsafe {
        PageHeap::format_slab(span, class).unwrap();
    }
    let SlabCommit::Inserted(a) = (unsafe { f.heap.commit_slab(span, class) }).unwrap() else {
        panic!()
    };
    let stats = f.heap.stats();
    assert_eq!(
        unsafe {
            f.heap
                .try_reuse(a.ptr, Some(old), Layout::from_size_align(60, 32).unwrap())
        },
        Ok(true)
    );
    assert_eq!(
        unsafe {
            f.heap
                .try_reuse(a.ptr, Some(old), Layout::from_size_align(65, 16).unwrap())
        },
        Ok(false)
    );
    assert_eq!(
        unsafe {
            f.heap
                .free(a.ptr, Some(Layout::from_size_align(65, 16).unwrap()))
        },
        Err(HeapError::LayoutMismatch)
    );
    // The first slot is 128-byte aligned even though its class guarantees only 64.
    // This exercises the slab-specific over-alignment check, not the address check.
    assert_eq!(a.ptr.as_ptr().addr() % 128, 0);
    let over_aligned = Layout::from_size_align(33, 128).unwrap();
    assert_eq!(
        unsafe { f.heap.try_reuse(a.ptr, Some(over_aligned), old) },
        Err(HeapError::LayoutMismatch)
    );
    assert_eq!(
        unsafe { f.heap.free(a.ptr, Some(over_aligned)) },
        Err(HeapError::LayoutMismatch)
    );
    assert_eq!(
        unsafe { f.heap.try_reuse(a.ptr, Some(old), over_aligned) },
        Ok(false)
    );
    assert_eq!(f.heap.stats(), stats);
    let info = f.heap.allocation_info(a.ptr).unwrap();
    assert_eq!(info.kind, AllocationKind::Slab(class));
    assert_eq!(info.capacity, 64);
    assert_eq!(info.span, span);
    assert!(unsafe { f.heap.free(span.start(), None) }.is_err());
    let interior = unsafe { std::ptr::NonNull::new_unchecked(a.ptr.as_ptr().add(1)) };
    assert!(unsafe { f.heap.free(interior, None) }.is_err());
    assert_eq!(f.heap.stats(), stats);
    assert_eq!(f.heap.allocation_info(a.ptr).unwrap().capacity, 64);
    match unsafe { f.heap.free(a.ptr, Some(old)) }.unwrap() {
        ReleaseAction::Pages(span) => f.release(span),
        ReleaseAction::None => panic!(),
    }
    assert_eq!(f.free_pages(), 4);
}

#[test]
fn charges_slots_and_pages_separately_and_retains_peak() {
    let mut f = Fixture::new(4);
    let layout = Layout::from_size_align(24, 8).unwrap();
    let AllocationPlan::Slab(class) = classify(layout).unwrap() else {
        panic!()
    };
    let slab = f.take(1, PAGE_SIZE).unwrap();
    unsafe { PageHeap::format_slab(slab, class) }.unwrap();
    let SlabCommit::Inserted(first) = (unsafe { f.heap.commit_slab(slab, class) }).unwrap() else {
        panic!()
    };
    let second = f.heap.try_alloc_small(class).unwrap().unwrap();
    assert_eq!(f.heap.stats().charged_bytes, 64);
    assert_eq!(f.heap.stats().backing_bytes, PAGE_SIZE);
    let span = f.take(3, PAGE_SIZE).unwrap();
    let large_layout = Layout::from_size_align(8193, 8).unwrap();
    let large = unsafe { f.heap.commit_large(span, large_layout) }.unwrap();
    assert_eq!(f.heap.stats().charged_bytes, 64 + 3 * PAGE_SIZE);
    assert_eq!(f.heap.stats().backing_bytes, 4 * PAGE_SIZE);
    for (ptr, layout) in [
        (first.ptr, layout),
        (second.ptr, layout),
        (large.ptr, large_layout),
    ] {
        if let ReleaseAction::Pages(span) = unsafe { f.heap.free(ptr, Some(layout)) }.unwrap() {
            f.release(span);
        }
    }
    assert_eq!(f.heap.stats().charged_bytes, 0);
    assert_eq!(f.heap.stats().backing_bytes, 0);
    assert_eq!(f.heap.stats().peak_charged_bytes, 64 + 3 * PAGE_SIZE);
}

#[test]
fn free_slot_remains_available_when_source_has_no_pages() {
    let mut f = Fixture::new(1);
    let AllocationPlan::Slab(class) = classify(Layout::from_size_align(24, 8).unwrap()).unwrap()
    else {
        panic!()
    };
    let slab = f.take(1, PAGE_SIZE).unwrap();
    unsafe { PageHeap::format_slab(slab, class) }.unwrap();
    let SlabCommit::Inserted(first) = (unsafe { f.heap.commit_slab(slab, class) }).unwrap() else {
        panic!()
    };
    assert_eq!(f.free_pages(), 0);
    assert_eq!(f.heap.largest_free_slot(), 32);
    let second = f.heap.try_alloc_small(class).unwrap().unwrap();
    for ptr in [first.ptr, second.ptr] {
        if let ReleaseAction::Pages(span) = unsafe { f.heap.free(ptr, None) }.unwrap() {
            f.release(span);
        }
    }
}

#[test]
fn dynamic_area_indices_preserve_independent_ownership_and_reuse_gaps() {
    use std::ptr::NonNull;
    let base = 0x1000_0000;
    let mut object = AreaIndex::<0>::new();
    let mut reservations = AreaIndex::<1>::new();
    let nodes: Vec<_> = (0..127)
        .map(|i| {
            NonNull::new(Box::into_raw(Box::new(
                Area::new(base + i * 2 * PAGE_SIZE, 1).unwrap(),
            )))
            .unwrap()
        })
        .collect();
    for k in 0..127 {
        let node = nodes[(k * 37) % 127];
        unsafe {
            object.insert(node).unwrap();
            reservations.insert(node).unwrap();
        }
    }
    assert_eq!(object.largest_gap(base, base + 254 * PAGE_SIZE), PAGE_SIZE);
    let mut live = [true; 127];
    for k in 0..127 {
        let i = (k * 53) % 127;
        let start = base + i * 2 * PAGE_SIZE;
        assert_eq!(object.remove(start), Some(nodes[i]));
        live[i] = false;
        for j in 0..127 {
            assert_eq!(object.find(base + j * 2 * PAGE_SIZE).is_some(), live[j]);
            assert!(reservations.find(base + j * 2 * PAGE_SIZE).is_some());
            assert!(object.find(base + j * 2 * PAGE_SIZE + PAGE_SIZE).is_none());
        }
    }
    assert_eq!(
        object.find_gap(base, base + 254 * PAGE_SIZE, 254 * PAGE_SIZE, PAGE_SIZE),
        Some(base)
    );
    for (i, node) in nodes.into_iter().enumerate() {
        assert_eq!(reservations.remove(base + i * 2 * PAGE_SIZE), Some(node));
        unsafe {
            drop(Box::from_raw(node.as_ptr()));
        }
    }
}

#[test]
fn area_indices_track_single_members_and_survive_index_moves() {
    use std::ptr::NonNull;
    let base = 0x1000_0000;
    let area = Box::new(Area::new(base, 1).unwrap());
    let node = NonNull::from(area.as_ref());
    let mut object = AreaIndex::<0>::new();
    let mut reservations = AreaIndex::<1>::new();
    let mut another_object_index = AreaIndex::<0>::new();
    assert!(unsafe { area.detached() });
    unsafe {
        object.insert(node).unwrap();
        reservations.insert(node).unwrap();
        assert!(!area.detached());
        assert_eq!(object.insert(node), Err(HeapError::Conflict));
        assert_eq!(another_object_index.insert(node), Err(HeapError::Conflict));
    }
    // Index headers may move; links must never point into an index header.
    let mut moved = Box::new(object);
    assert_eq!(moved.find(base + PAGE_SIZE - 1), Some(node));
    assert_eq!(moved.find(base + PAGE_SIZE), None);
    assert_eq!(moved.remove(base + 1), None);
    assert_eq!(moved.remove(base), Some(node));
    assert!(unsafe { area.detached() });
    assert_eq!(reservations.find(base), Some(node));
    assert_eq!(moved.remove(base), None);
    unsafe { another_object_index.insert(node).unwrap() };
    assert_eq!(another_object_index.remove(base), Some(node));
    assert_eq!(reservations.remove(base), Some(node));
    assert_eq!(reservations.largest_gap(base, base + PAGE_SIZE), PAGE_SIZE);
}

#[test]
fn area_indices_allow_independent_concurrent_indices() {
    use std::{ptr::NonNull, sync::Barrier, thread};
    let nodes: Vec<_> = (0..4)
        .map(|i| Area::new(0x1000_0000 + i * 2 * PAGE_SIZE, 1).unwrap())
        .collect();
    let barrier = Barrier::new(2);
    fn exercise<const I: usize>(nodes: &[Area], barrier: &Barrier) {
        let mut index = AreaIndex::<I>::new();
        for _ in 0..4 {
            for area in nodes.iter().rev() {
                unsafe { index.insert(NonNull::from(area)).unwrap() };
            }
            barrier.wait();
            for area in nodes {
                assert_eq!(index.find(area.end - 1), Some(NonNull::from(area)));
                assert_eq!(index.remove(area.start), Some(NonNull::from(area)));
            }
            barrier.wait();
        }
    }
    thread::scope(|scope| {
        scope.spawn(|| exercise::<0>(&nodes, &barrier));
        scope.spawn(|| exercise::<1>(&nodes, &barrier));
    });
    assert!(nodes.iter().all(|area| unsafe { area.detached() }));
}

#[test]
fn large_virtual_window_needs_no_per_page_metadata() {
    use std::ptr::NonNull;
    let start = 0xffff800000000000usize;
    let bytes = 1usize << 46;
    let window = unsafe {
        PageWindow::new(
            NonNull::new(std::ptr::without_provenance_mut(start)).unwrap(),
            bytes / PAGE_SIZE,
        )
    }
    .unwrap();
    let heap = unsafe { PageHeap::new(window) }.unwrap();
    assert_eq!(heap.stats(), HeapStats::default());
    let areas = AreaIndex::<1>::new();
    assert_eq!(areas.largest_gap(start, start + bytes), bytes);
    assert_eq!(
        areas.find_gap(start, start + bytes, 3 * PAGE_SIZE, 65536),
        Some(start)
    );
}
