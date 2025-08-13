// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

// This code is based on https://github.com/rust-osdev/linked-list-allocator/blob/main/src/hole.rs.
// Copyright (c) 2016 Philipp Oppermann
// SPDX-LICENSE: MIT

use crate::{
    allocator::block::{
        get_overhead_and_size, used_block_hdr_for_allocation,
        used_block_hdr_for_allocation_unknown_align, UsedBlockHdr, UsedBlockPad, GRANULARITY,
        SIZE_USED,
    },
    support::{align_down_size, align_up, align_up_size},
};
use core::{
    alloc::{Layout, LayoutError},
    mem,
    mem::{align_of, size_of},
    ptr::{null_mut, NonNull},
};

/// A sorted list of holes. It uses the the holes itself to store its nodes.
pub struct HoleList {
    pub(crate) first: Hole, // dummy
    pub(crate) bottom: *mut u8,
    pub(crate) top: *mut u8,
    pub(crate) pending_extend: u8,
}

pub(crate) struct Cursor {
    prev: NonNull<Hole>,
    hole: NonNull<Hole>,
    top: *mut u8,
}

/// A block containing free memory. It points to the next hole and thus forms a linked list.
pub(crate) struct Hole {
    pub size: usize,
    pub next: Option<NonNull<Hole>>,
}

/// Basic information about a hole.
#[derive(Debug, Clone, Copy)]
struct HoleInfo {
    size: usize,
    addr: *mut u8,
}

impl Cursor {
    fn next(mut self) -> Option<Self> {
        unsafe {
            self.hole.as_mut().next.map(|nhole| Cursor {
                prev: self.hole,
                hole: nhole,
                top: self.top,
            })
        }
    }

    fn current(&self) -> &Hole {
        unsafe { self.hole.as_ref() }
    }

    fn previous(&self) -> &Hole {
        unsafe { self.prev.as_ref() }
    }

    // On success, it returns the new allocation, and the linked list has been updated
    // to accomodate any new holes and allocation. On error, it returns the cursor
    // unmodified, and has made no changes to the linked list of holes.
    fn split_current(self, required_layout: &Layout) -> Result<(NonNull<u8>, usize), Self> {
        let alloc_ptr;
        let mut alloc_size;
        let back_padding;
        let hole_addr_u8 = unsafe { NonNull::new_unchecked(self.hole.as_ptr().cast::<u8>()) };

        // Here we create a scope, JUST to make sure that any created references do not
        // live to the point where we start doing pointer surgery below.
        {
            let hole_size = self.current().size;
            let (max_overhead, search_size) =
                if let Some((max_overhead, search_size)) = get_overhead_and_size(required_layout) {
                    (max_overhead, search_size)
                } else {
                    return Err(self);
                };

            // Quick check: If the new item is larger than the current hole, it's never gunna
            // work. Go ahead and bail early to save ourselves some math.
            if hole_size < search_size {
                return Err(self);
            }

            // Decide the starting address of the payload
            let unaligned_ptr = hole_addr_u8.as_ptr() as usize + mem::size_of::<UsedBlockHdr>();
            alloc_ptr = unsafe {
                NonNull::new_unchecked(
                    (unaligned_ptr.wrapping_add(required_layout.align() - 1)
                        & !(required_layout.align() - 1)) as *mut u8,
                )
            };

            if required_layout.align() < GRANULARITY {
                debug_assert_eq!(unaligned_ptr, alloc_ptr.as_ptr() as usize);
            } else {
                debug_assert_ne!(unaligned_ptr, alloc_ptr.as_ptr() as usize);
            }

            // Calculate the actual overhead and the final block size of the
            // used block being created here
            let overhead = alloc_ptr.as_ptr() as usize - hole_addr_u8.as_ptr() as usize;
            debug_assert!(overhead <= max_overhead);

            let new_size = overhead + required_layout.size();
            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
            debug_assert!(new_size <= search_size);
            alloc_size = new_size;
            debug_assert!(alloc_size <= hole_size);
            // Okay, time to move onto the back padding.
            back_padding = if hole_size == new_size {
                None
            } else {
                // NOTE: Because we always use `HoleList::align_layout`, the size of
                // the new allocation is always "rounded up" to cover any partial gaps that
                // would have occurred. For this reason, we DON'T need to "round up"
                // to account for an unaligned hole spot.
                let back_padding_size = hole_size - new_size;
                let back_padding_start = hole_addr_u8.as_ptr().wrapping_add(new_size);

                // Will the proposed new back padding actually fit in the old hole slot?
                if back_padding_size >= GRANULARITY {
                    // Yes, it does! Place a back padding node
                    Some(HoleInfo {
                        addr: back_padding_start,
                        size: back_padding_size,
                    })
                } else {
                    // No, it does not. not split this hole.
                    alloc_size = hole_size;
                    None
                }
            };
        }

        ////////////////////////////////////////////////////////////////////////////
        // This is where we actually perform surgery on the linked list.
        ////////////////////////////////////////////////////////////////////////////
        let Cursor {
            mut prev, mut hole, ..
        } = self;
        // Remove the current location from the previous node
        unsafe {
            prev.as_mut().next = None;
        }
        // Take the next node out of our current node
        let maybe_next_addr: Option<NonNull<Hole>> = unsafe { hole.as_mut().next.take() };

        // As of now, the old `Hole` is no more. We are about to replace it with one or more of
        // the front padding, the allocation, and the back padding.

        match back_padding {
            None => {
                // No padding at all, how lucky! We still need to connect the PREVIOUS node
                // to the NEXT node, if there was one
                unsafe {
                    prev.as_mut().next = maybe_next_addr;
                }
            }
            Some(singlepad) => unsafe {
                // We have front padding OR back padding, but not both.
                //
                // Replace the old node with the new single node. We need to stitch the new node
                // into the linked list. Start by writing the padding into the proper location
                let singlepad_ptr = singlepad.addr.cast::<Hole>();
                singlepad_ptr.write(Hole {
                    size: singlepad.size,
                    // If the old hole had a next pointer, the single padding now takes
                    // "ownership" of that link
                    next: maybe_next_addr,
                });

                // Then connect the OLD previous to the NEW single padding
                prev.as_mut().next = Some(NonNull::new_unchecked(singlepad_ptr));
            },
        }

        unsafe {
            // Turn `block` into a used memory block and initialize the used block
            // header. `prev_phys_block` is already set.
            let mut block = hole_addr_u8.cast::<UsedBlockHdr>();
            block.as_mut().common.size = alloc_size | SIZE_USED;

            // Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            if required_layout.align() >= GRANULARITY {
                (*UsedBlockPad::get_for_allocation(alloc_ptr)).block_hdr = block;
            }

            //crate::trace!("alloc_ptr: {:?}, alloc_size: {}", alloc_ptr, alloc_size);
        }

        // Well that went swimmingly! Hand off the allocation, with surgery performed successfully!
        Ok((alloc_ptr, alloc_size))
    }
}

// See if we can extend this hole towards the end of the allocation region
// If so: increase the size of the node. If no: keep the node as-is
fn check_merge_top(mut node: NonNull<Hole>, top: *mut u8) {
    let node_u8 = node.as_ptr().cast::<u8>();
    let node_sz = unsafe { node.as_ref().size };

    // If this is the last node, we need to see if we need to merge to the end
    let end = node_u8.wrapping_add(node_sz);
    let hole_layout = Layout::new::<Hole>();
    if end < top {
        let next_hole_end = align_up(end, hole_layout.align()).wrapping_add(hole_layout.size());

        if next_hole_end > top {
            let offset = (top as usize) - (end as usize);
            unsafe {
                node.as_mut().size += offset;
            }
        }
    }
}

// See if we can scoot this hole back to the bottom of the allocation region
// If so: create and return the new hole. If not: return the existing hole
fn check_merge_bottom(node: NonNull<Hole>, bottom: *mut u8) -> NonNull<Hole> {
    debug_assert_eq!(bottom as usize % align_of::<Hole>(), 0);

    if bottom.wrapping_add(core::mem::size_of::<Hole>()) > node.as_ptr().cast::<u8>() {
        let offset = (node.as_ptr() as usize) - (bottom as usize);
        let size = unsafe { node.as_ref() }.size + offset;
        unsafe { make_hole(bottom, size) }
    } else {
        node
    }
}

impl HoleList {
    /// Creates an empty `HoleList`.
    pub const fn empty() -> HoleList {
        HoleList {
            first: Hole {
                size: 0,
                next: None,
            },
            bottom: null_mut(),
            top: null_mut(),
            pending_extend: 0,
        }
    }

    pub(crate) fn cursor(&mut self) -> Option<Cursor> {
        if let Some(hole) = self.first.next {
            Some(Cursor {
                hole,
                prev: NonNull::new(&mut self.first)?,
                top: self.top,
            })
        } else {
            None
        }
    }

    #[cfg(any(test, fuzzing))]
    #[allow(dead_code)]
    pub(crate) fn debug(&mut self) {
        if let Some(cursor) = self.cursor() {
            let mut cursor = cursor;
            loop {
                crate::kprintln!(
                    "prev: {:?}[{}], hole: {:?}[{}]",
                    cursor.previous() as *const Hole,
                    cursor.previous().size,
                    cursor.current() as *const Hole,
                    cursor.current().size,
                );
                if let Some(c) = cursor.next() {
                    cursor = c;
                } else {
                    crate::kprintln!("Done!");
                    return;
                }
            }
        } else {
            crate::kprintln!("No holes");
        }
    }

    /// Creates a `HoleList` that contains the given hole.
    ///
    /// The `hole_addr` pointer is automatically aligned, so the `bottom`
    /// field might be larger than the given `hole_addr`.
    ///
    /// The given `hole_size` must be large enough to store the required
    /// metadata, otherwise this function will panic. Depending on the
    /// alignment of the `hole_addr` pointer, the minimum size is between
    /// `2 * size_of::<usize>` and `3 * size_of::<usize>`.
    ///
    /// The usable size for allocations will be truncated to the nearest
    /// alignment of `align_of::<usize>`. Any extra bytes left at the end
    /// will be reclaimed once sufficient additional space is given to
    /// [`extend`][crate::Heap::extend].
    ///
    /// # Safety
    ///
    /// This function is unsafe because it creates a hole at the given `hole_addr`.
    /// This can cause undefined behavior if this address is invalid or if memory from the
    /// `[hole_addr, hole_addr+size)` range is used somewhere else.
    pub unsafe fn new(hole_addr: *mut u8, hole_size: usize) -> HoleList {
        debug_assert!(GRANULARITY >= size_of::<Hole>());
        debug_assert!(hole_size >= GRANULARITY);

        let aligned_hole_addr = align_up(hole_addr, GRANULARITY);
        let requested_hole_size =
            hole_size.saturating_sub(aligned_hole_addr.wrapping_sub(hole_addr as usize) as usize);
        let aligned_hole_size = align_down_size(requested_hole_size, GRANULARITY);
        assert!(aligned_hole_size >= GRANULARITY);

        let ptr = aligned_hole_addr as *mut Hole;
        ptr.write(Hole {
            size: aligned_hole_size,
            next: None,
        });

        assert_eq!(
            hole_addr.wrapping_add(hole_size),
            aligned_hole_addr.wrapping_add(requested_hole_size)
        );

        HoleList {
            first: Hole {
                size: 0,
                next: Some(NonNull::new_unchecked(ptr)),
            },
            bottom: aligned_hole_addr,
            top: aligned_hole_addr.wrapping_add(aligned_hole_size),
            pending_extend: (requested_hole_size - aligned_hole_size) as u8,
        }
    }

    /// Aligns the given layout for use with `HoleList`.
    ///
    /// Returns a layout with size increased to fit at least `HoleList::min_size` and proper
    /// alignment of a `Hole`.
    ///
    /// The [`allocate_first_fit`][HoleList::allocate_first_fit] and
    /// [`deallocate`][HoleList::deallocate] methods perform the required alignment
    /// themselves, so calling this function manually is not necessary.
    pub fn align_layout(layout: &Layout) -> Result<Layout, LayoutError> {
        let mut size = layout.size();
        if size < Self::min_size() {
            size = Self::min_size();
        }
        let size = align_up_size(size, mem::align_of::<Hole>());
        Layout::from_size_align(size, layout.align())
    }

    /// Searches the list for a big enough hole.
    ///
    /// A hole is big enough if it can hold an allocation of `layout.size()` bytes with
    /// the given `layout.align()`. If such a hole is found in the list, a block of the
    /// required size is allocated from it. Then the start address of that
    /// block and the aligned layout are returned. The automatic layout alignment is required
    /// because the `HoleList` has some additional layout requirements for each memory block.
    ///
    /// This function uses the “first fit” strategy, so it uses the first hole that is big
    /// enough. Thus the runtime is in O(n) but it should be reasonably fast for small allocations.
    //
    // NOTE: We could probably replace this with an `Option` instead of a `Result` in a later
    // release to remove this clippy warning
    #[allow(clippy::result_unit_err)]
    pub fn allocate_first_fit(&mut self, layout: &Layout) -> Result<(NonNull<u8>, usize), ()> {
        let aligned_layout = Self::align_layout(layout).map_err(|_| ())?;
        let mut cursor = self.cursor().ok_or(())?;

        loop {
            match cursor.split_current(&aligned_layout) {
                Ok((ptr, hole_size)) => {
                    return Ok((ptr, hole_size));
                }
                Err(curs) => {
                    cursor = curs.next().ok_or(())?;
                }
            }
        }
    }

    /// Frees the allocation given by `ptr` and `layout`.
    ///
    /// This function walks the list and inserts the given block at the correct place. If the freed
    /// block is adjacent to another free block, the blocks are merged again.
    /// This operation is in `O(n)` since the list needs to be sorted by address.
    ///
    /// [`allocate_first_fit`]: HoleList::allocate_first_fit
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer returned by a call to the [`allocate_first_fit`] function with
    /// identical layout. Undefined behavior may occur for invalid arguments.
    /// The function performs exactly the same layout adjustments as [`allocate_first_fit`] and
    /// returns the aligned layout.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: &Layout) -> usize {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let Some(old_block) = used_block_hdr_for_allocation(ptr, layout.align()) else {
            return 0;
        };
        let old_block = old_block.cast::<UsedBlockHdr>();
        let hole_addr_u8 = old_block.as_ptr() as *mut u8;
        let hole_size = old_block.as_ref().common.size - SIZE_USED;

        deallocate(self, hole_addr_u8, hole_size);
        hole_size
    }

    pub unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let Some(old_block) = used_block_hdr_for_allocation_unknown_align(ptr) else {
            return 0;
        };
        let old_block = old_block.cast::<UsedBlockHdr>();
        let hole_addr_u8 = old_block.as_ptr() as *mut u8;
        let hole_size = old_block.as_ref().common.size - SIZE_USED;

        deallocate(self, hole_addr_u8, hole_size);
        hole_size
    }

    /// Returns the minimal allocation size. Smaller allocations or deallocations are not allowed.
    pub fn min_size() -> usize {
        GRANULARITY as usize
    }

    /// Returns information about the first hole for test purposes.
    #[cfg(test)]
    pub fn first_hole(&self) -> Option<(*const u8, usize)> {
        self.first.next.as_ref().map(|hole| {
            (hole.as_ptr() as *mut u8 as *const u8, unsafe {
                hole.as_ref().size
            })
        })
    }

    pub(crate) unsafe fn extend(&mut self, by: usize) {
        assert!(!self.top.is_null(), "tried to extend an empty heap");

        let top = self.top;

        let dead_space = top.align_offset(align_of::<Hole>());
        debug_assert_eq!(
            0, dead_space,
            "dead space detected during extend: {} bytes. This means top was unaligned",
            dead_space
        );

        debug_assert!(
            (self.pending_extend as usize) < Self::min_size(),
            "pending extend was larger than expected"
        );

        // join this extend request with any pending (but not yet acted on) extension
        let extend_by = self.pending_extend as usize + by;

        let minimum_extend = Self::min_size();
        if extend_by < minimum_extend {
            self.pending_extend = extend_by as u8;
            return;
        }

        // only extend up to another valid boundary
        let new_hole_size = align_down_size(extend_by, align_of::<Hole>());
        deallocate(self, top, new_hole_size);
        self.top = top.add(new_hole_size);

        // save extra bytes given to extend that weren't aligned to the hole size
        self.pending_extend = (extend_by - new_hole_size) as u8;
    }
}

unsafe fn make_hole(addr: *mut u8, size: usize) -> NonNull<Hole> {
    let hole_addr = addr.cast::<Hole>();
    debug_assert_eq!(
        addr as usize % align_of::<Hole>(),
        0,
        "Hole address not aligned!",
    );
    hole_addr.write(Hole { size, next: None });
    NonNull::new_unchecked(hole_addr)
}

impl Cursor {
    fn try_insert_back(self, node: NonNull<Hole>, bottom: *mut u8) -> Result<Self, Self> {
        // Covers the case where the new hole exists BEFORE the current pointer,
        // which only happens when previous is the stub pointer
        if node < self.hole {
            let node_u8 = node.as_ptr().cast::<u8>();
            let node_size = unsafe { node.as_ref().size };
            let hole_u8 = self.hole.as_ptr().cast::<u8>();

            assert!(
                node_u8.wrapping_add(node_size) <= hole_u8,
                "Freed node aliases existing hole! Bad free?",
            );
            debug_assert_eq!(self.previous().size, 0);

            let Cursor {
                mut prev,
                hole,
                top,
            } = self;
            unsafe {
                let mut node = check_merge_bottom(node, bottom);
                prev.as_mut().next = Some(node);
                node.as_mut().next = Some(hole);
            }
            Ok(Cursor {
                prev,
                hole: node,
                top,
            })
        } else {
            Err(self)
        }
    }

    fn try_insert_after(&mut self, mut node: NonNull<Hole>) -> Result<(), ()> {
        let node_u8 = node.as_ptr().cast::<u8>();
        let node_size = unsafe { node.as_ref().size };

        // If we have a next, does the node overlap next?
        if let Some(next) = self.current().next.as_ref() {
            if node < *next {
                let node_u8 = node_u8 as *const u8;
                assert!(
                    node_u8.wrapping_add(node_size) <= next.as_ptr().cast::<u8>(),
                    "Freed node aliases existing hole! Bad free?",
                );
            } else {
                // The new hole isn't between current and next.
                return Err(());
            }
        }

        // At this point, we either have no "next" pointer, or the hole is
        // between current and "next". The following assert can only trigger
        // if we've gotten our list out of order.
        debug_assert!(self.hole < node, "Hole list out of order?");

        let hole_u8 = self.hole.as_ptr().cast::<u8>();
        let hole_size = self.current().size;

        // Does hole overlap node?
        assert!(
            hole_u8.wrapping_add(hole_size) <= node_u8,
            "Freed node ({:?}) aliases existing hole ({:?}[{}])! Bad free?",
            node_u8,
            hole_u8,
            hole_size,
        );

        // All good! Let's insert that after.
        unsafe {
            let maybe_next = self.hole.as_mut().next.replace(node);
            node.as_mut().next = maybe_next;
        }

        Ok(())
    }

    // Merge the current node with up to n following nodes
    fn try_merge_next_n(self, max: usize) {
        let Cursor {
            prev: _,
            mut hole,
            top,
            ..
        } = self;

        for _ in 0..max {
            // Is there a next node?
            let mut next = if let Some(next) = unsafe { hole.as_mut() }.next.as_ref() {
                *next
            } else {
                // Since there is no NEXT node, we need to check whether the current
                // hole SHOULD extend to the end, but doesn't. This would happen when
                // there isn't enough remaining space to place a hole after the current
                // node's placement.
                check_merge_top(hole, top);
                return;
            };

            // Can we directly merge these? e.g. are they touching?
            //
            // NOTE: Because we always use `HoleList::align_layout`, the size of
            // the new hole is always "rounded up" to cover any partial gaps that
            // would have occurred. For this reason, we DON'T need to "round up"
            // to account for an unaligned hole spot.
            let hole_u8 = hole.as_ptr().cast::<u8>();
            let hole_sz = unsafe { hole.as_ref().size };
            let next_u8 = next.as_ptr().cast::<u8>();
            let end = hole_u8.wrapping_add(hole_sz);

            let touching = end == next_u8;

            if touching {
                let next_sz;
                let next_next;
                unsafe {
                    let next_mut = next.as_mut();
                    next_sz = next_mut.size;
                    next_next = next_mut.next.take();
                }
                unsafe {
                    let hole_mut = hole.as_mut();
                    hole_mut.next = next_next;
                    hole_mut.size += next_sz;
                }
                // Okay, we just merged the next item. DON'T move the cursor, as we can
                // just try to merge the next_next, which is now our next.
            } else {
                // Welp, not touching, can't merge. Move to the next node.
                hole = next;
            }
        }
    }
}

/// Frees the allocation given by `(addr, size)`. It starts at the given hole and walks the list to
/// find the correct place (the list is sorted by address).
fn deallocate(list: &mut HoleList, addr: *mut u8, size: usize) {
    // Start off by just making this allocation a hole where it stands.
    // We'll attempt to merge it with other nodes once we figure out where
    // it should live
    let hole = unsafe { make_hole(addr, size) };

    // Now, try to get a cursor to the list - this only works if we have at least
    // one non-"dummy" hole in the list
    let cursor = if let Some(cursor) = list.cursor() {
        cursor
    } else {
        // Oh hey, there are no "real" holes at all. That means this just
        // becomes the only "real" hole! Check if this is touching the end
        // or the beginning of the allocation range
        let hole = check_merge_bottom(hole, list.bottom);
        check_merge_top(hole, list.top);
        list.first.next = Some(hole);
        return;
    };

    // First, check if we can just insert this node at the top of the list. If the
    // insertion succeeded, then our cursor now points to the NEW node, behind the
    // previous location the cursor was pointing to.
    //
    // Otherwise, our cursor will point at the current non-"dummy" head of the list
    let (cursor, n) = match cursor.try_insert_back(hole, list.bottom) {
        Ok(cursor) => {
            // Yup! It lives at the front of the list. Hooray! Attempt to merge
            // it with just ONE next node, since it is at the front of the list
            (cursor, 1)
        }
        Err(mut cursor) => {
            // Nope. It lives somewhere else. Advance the list until we find its home
            while let Err(()) = cursor.try_insert_after(hole) {
                cursor = cursor
                    .next()
                    .expect("Reached end of holes without finding deallocation hole!");
            }
            // Great! We found a home for it, our cursor is now JUST BEFORE the new
            // node we inserted, so we need to try to merge up to twice: One to combine
            // the current node to the new node, then once more to combine the new node
            // with the node after that.
            (cursor, 2)
        }
    };

    // We now need to merge up to two times to combine the current node with the next
    // two nodes.
    cursor.try_merge_next_n(n);
}
