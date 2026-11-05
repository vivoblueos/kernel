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

//! Interval ownership and gap queries over Infra's intrusive AVL tree.
use super::{ClassId, HeapError, PageSpan, PAGE_SIZE};
use blueos_infra::{
    avl::{AvlLink, AvlTree},
    intrusive::Adapter,
};
use core::{
    alloc::Layout,
    cell::UnsafeCell,
    cmp::Ordering,
    mem::{offset_of, size_of},
    ops::ControlFlow,
    ptr::NonNull,
};

#[derive(Clone, Copy)]
pub(crate) enum Kind {
    Empty,
    Slab(ClassId),
    Large(Layout),
}

struct AreaAdapter<const I: usize>;
impl<const I: usize> const Adapter<Area> for AreaAdapter<I> {
    fn offset() -> usize {
        assert!(I < 2);
        offset_of!(Area, links) + I * size_of::<AvlLink<Area>>()
    }
}

/// Stable metadata supplied by a page source, never allocated by the raw heap.
/// Index 0 belongs to the object heap; index 1 belongs to VA reservations.
pub struct Area {
    pub start: usize,
    pub end: usize,
    links: [AvlLink<Area>; 2],
    kind: UnsafeCell<Kind>,
    payload: UnsafeCell<Option<NonNull<u8>>>,
}

impl Area {
    pub fn new(start: usize, pages: usize) -> Result<Self, HeapError> {
        let end = start
            .checked_add(
                pages
                    .checked_mul(PAGE_SIZE)
                    .ok_or(HeapError::InvalidGeometry)?,
            )
            .ok_or(HeapError::InvalidGeometry)?;
        if pages == 0 || start & (PAGE_SIZE - 1) != 0 {
            return Err(HeapError::InvalidGeometry);
        }
        Ok(Self {
            start,
            end,
            links: [AvlLink::new(), AvlLink::new()],
            kind: UnsafeCell::new(Kind::Empty),
            payload: UnsafeCell::new(None),
        })
    }
    pub(crate) unsafe fn kind(&self) -> Kind {
        *self.kind.get()
    }
    pub(crate) unsafe fn set_kind(&self, kind: Kind) {
        *self.kind.get() = kind;
    }
    /// Whether the object heap has detached this descriptor.
    ///
    /// # Safety
    /// Caller owns the allocation or holds the object index lock.
    pub unsafe fn detached(&self) -> bool {
        unsafe { !self.links[0].is_linked() }
    }
    pub(crate) unsafe fn attach(&self, start: NonNull<u8>) {
        *self.payload.get() = Some(start);
    }
    pub(crate) unsafe fn span(node: NonNull<Self>) -> PageSpan {
        let area = node.as_ref();
        PageSpan {
            start: (*area.payload.get()).expect("attached payload provenance"),
            pages: (area.end - area.start) / PAGE_SIZE,
            area: Some(node),
        }
    }
}
// Each index and the kind field have a distinct external owner/lock. Ranges
// stay immutable until both indices have detached the descriptor.
unsafe impl Send for Area {}
unsafe impl Sync for Area {}

/// Non-overlapping intervals indexed by start address. Lookup, insertion and
/// removal are O(log N); gap queries traverse intervals in O(N).
pub struct AreaIndex<const I: usize> {
    tree: AvlTree<Area, AreaAdapter<I>>,
}
impl<const I: usize> Default for AreaIndex<I> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const I: usize> AreaIndex<I> {
    pub const fn new() -> Self {
        assert!(I < 2);
        Self {
            tree: AvlTree::new(),
        }
    }

    /// Insert a stable, non-overlapping descriptor without allocating.
    ///
    /// # Safety
    /// Caller keeps nodes and ranges stable until removal, serializes this
    /// index, and retains backing for every shared reference to a linked node.
    pub unsafe fn insert(&mut self, node: NonNull<Area>) -> Result<(), HeapError> {
        let area = node.as_ref();
        if self.overlaps(area.start, area.end) {
            return Err(HeapError::Conflict);
        }
        self.tree
            .insert(node, |a, b| a.start.cmp(&b.start))
            .map_err(|_| HeapError::Conflict)
    }

    pub fn find(&self, address: usize) -> Option<NonNull<Area>> {
        self.tree.find(|area| {
            if address < area.start {
                Ordering::Less
            } else if address >= area.end {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        })
    }
    pub fn overlaps(&self, start: usize, end: usize) -> bool {
        self.tree
            .find(|area| {
                if end <= area.start {
                    Ordering::Less
                } else if start >= area.end {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            })
            .is_some()
    }
    pub fn remove(&mut self, start: usize) -> Option<NonNull<Area>> {
        self.tree.remove(|area| start.cmp(&area.start))
    }

    /// Gaps are implicit, so deleting a reservation coalesces space without
    /// allocating free-area nodes. Traversal uses only the bounded AVL stack.
    pub fn find_gap(&self, start: usize, end: usize, bytes: usize, align: usize) -> Option<usize> {
        if bytes == 0 || !align.is_power_of_two() {
            return None;
        }
        fn aligned(start: usize, bytes: usize, align: usize, end: usize) -> Option<usize> {
            let p = start.checked_add(align - 1)? & !(align - 1);
            (p.checked_add(bytes)? <= end).then_some(p)
        }
        let mut cursor = start;
        match self.tree.try_for_each(|area| {
            if let Some(p) = aligned(cursor, bytes, align, area.start.min(end)) {
                return ControlFlow::Break(p);
            }
            cursor = cursor.max(area.end);
            ControlFlow::Continue(())
        }) {
            ControlFlow::Break(p) => Some(p),
            ControlFlow::Continue(()) => aligned(cursor, bytes, align, end),
        }
    }
    pub fn largest_gap(&self, start: usize, end: usize) -> usize {
        let mut cursor = start;
        let mut max = 0;
        let _completed = self.tree.try_for_each::<(), _>(|area| {
            max = max.max(area.start.saturating_sub(cursor));
            cursor = cursor.max(area.end);
            ControlFlow::Continue(())
        });
        max.max(end.saturating_sub(cursor))
    }
}
