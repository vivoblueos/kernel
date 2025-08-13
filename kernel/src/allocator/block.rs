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

// This code is based on https://github.com/yvt/rlsf/blob/main/crates/rlsf/src/tlsf.rs.
// Copyright 2021 yvt
// SPDX-LICENSE: MIT

use core::{
    alloc::Layout,
    ptr::{addr_of, NonNull},
};

/// The allocation granularity.
///
/// It is `size_of::<usize>() * 4` bytes, which is the minimum size of a
/// free block.
pub(crate) const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;

pub(crate) const GRANULARITY_LOG2: u32 = GRANULARITY.trailing_zeros();

/// The header of a memory block.
// The header is actually aligned at `size_of::<usize>() * 4`-byte boundaries
// but the alignment is set to a half value here not to introduce a padding at
// the end of this struct.
#[repr(C)]
#[cfg_attr(target_pointer_width = "16", repr(align(4)))]
#[cfg_attr(target_pointer_width = "32", repr(align(8)))]
#[cfg_attr(target_pointer_width = "64", repr(align(16)))]
#[derive(Debug)]
pub(crate) struct BlockHdr {
    /// The size of the whole memory block, including the header.
    ///
    ///  - `bit[0]` ([`SIZE_USED`]) indicates whether the block is a used memory
    ///    block or not.
    ///
    ///  - `bit[1]` ([`SIZE_LAST_IN_POOL`]) indicates whether the block is the
    ///    last one of the pool or not.
    ///
    ///  - `bit[GRANULARITY_LOG2..]` ([`SIZE_SIZE_MASK`]) represents the size.
    ///
    pub(crate) size: usize,
    pub(crate) prev_phys_block: Option<NonNull<BlockHdr>>,
}

/// The bit of [`BlockHdr::size`] indicating whether the block is a used memory
/// block or not.
pub(crate) const SIZE_USED: usize = 1;
/// The bit of [`BlockHdr::size`] indicating whether the block is a sentinel
/// (the last block in a memory pool) or not. If this bit is set, [`SIZE_USED`]
/// must be set, too (`SIZE_SENTINEL ⟹ SIZE_USED`).
pub(crate) const SIZE_SENTINEL: usize = 2;
/// The bits of [`BlockHdr::size`] indicating the block's size.
pub(crate) const SIZE_SIZE_MASK: usize = !((1 << GRANULARITY_LOG2) - 1);

impl BlockHdr {
    #[inline]
    pub(crate) fn new(size: usize, prev_phys_block: Option<NonNull<BlockHdr>>) -> Self {
        Self {
            size,
            prev_phys_block,
        }
    }

    /// Get the next block, assuming it exists.
    ///
    /// # Safety
    ///
    /// `self` must have a next block (it must not be the sentinel block in a
    /// pool).
    #[inline]
    pub(crate) unsafe fn next_phys_block(&self) -> NonNull<BlockHdr> {
        debug_assert!(
            (self.size & SIZE_SENTINEL) == 0,
            "`self` must not be a sentinel"
        );

        // Safety: Since `self.size & SIZE_LAST_IN_POOL` is not lying, the
        //         next block should exist at a non-null location.
        NonNull::new_unchecked((self as *const _ as *mut u8).add(self.size & SIZE_SIZE_MASK)).cast()
    }
}

/// The header of a used memory block. It's `GRANULARITY / 2` bytes long.
///
/// The payload immediately follows this header. However, if the alignment
/// requirement is greater than or equal to [`GRANULARITY`], an up to
/// `align - GRANULARITY / 2` bytes long padding will be inserted between them,
/// and the last part of the padding ([`UsedBlockPad`]) will encode where the
/// header is located.
#[repr(C)]
#[derive(Debug)]
pub(crate) struct UsedBlockHdr {
    pub(crate) common: BlockHdr,
}

/// In a used memory block with an alignment requirement larger than or equal to
/// `GRANULARITY`, the payload is preceded by this structure.
#[derive(Debug)]
#[repr(C)]
pub(crate) struct UsedBlockPad {
    pub(crate) block_hdr: NonNull<UsedBlockHdr>,
}

impl UsedBlockPad {
    #[inline]
    pub(crate) fn get_for_allocation(ptr: NonNull<u8>) -> *mut Self {
        ptr.cast::<Self>().as_ptr().wrapping_sub(1)
    }
}

// The extra bytes consumed by the header and padding.
//
// After choosing a free block, we need to adjust the payload's location
// to meet the alignment requirement. Every block is aligned to
// `GRANULARITY` bytes. `size_of::<UsedBlockHdr>` is `GRANULARITY / 2`
// bytes, so the address immediately following `UsedBlockHdr` is only
// aligned to `GRANULARITY / 2` bytes. Consequently, we need to insert
// a padding containing at most `max(align - GRANULARITY / 2, 0)` bytes.
#[inline]
pub(crate) fn get_overhead_and_size(layout: &Layout) -> Option<(usize, usize)> {
    let max_overhead =
        layout.align().saturating_sub(GRANULARITY / 2) + core::mem::size_of::<UsedBlockHdr>();
    // Search for a suitable free block
    let search_size = layout.size().checked_add(max_overhead)?;
    let search_size = search_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
    Some((max_overhead, search_size))
}

/// Find the `UsedBlockHdr` for an allocation (any `NonNull<u8>` returned by
/// our allocation functions).
///
/// # Safety
///
///  - `ptr` must point to an allocated memory block returned by
///      `Self::{allocate, reallocate}`.
///
///  - The memory block must have been allocated with the same alignment
///    ([`Layout::align`]) as `align`.
///
#[inline]
pub(crate) unsafe fn used_block_hdr_for_allocation(
    ptr: NonNull<u8>,
    align: usize,
) -> Option<NonNull<UsedBlockHdr>> {
    let block_hdr = if align >= GRANULARITY {
        // Read the header pointer
        (*UsedBlockPad::get_for_allocation(ptr)).block_hdr
    } else {
        NonNull::new_unchecked(ptr.as_ptr().sub(GRANULARITY / 2)).cast()
    };

    if block_hdr.as_ref().common.size & SIZE_USED == 0
        || block_hdr.as_ref().common.size & SIZE_SENTINEL == SIZE_SENTINEL
    {
        log::warn!("0x{:p} is already freed", ptr.as_ptr());
        return None;
    }

    debug_assert_ne!(block_hdr.as_ref().common.size & SIZE_SIZE_MASK, 0);
    debug_assert_eq!(block_hdr, used_block_hdr_for_allocation_unknown_align(ptr)?);

    Some(block_hdr)
}

/// Find the `UsedBlockHdr` for an allocation (any `NonNull<u8>` returned by
/// our allocation functions) with an unknown alignment.
///
/// Unlike `used_block_hdr_for_allocation`, this function does not require
/// knowing the allocation's alignment but might be less efficient.
///
/// # Safety
///
///  - `ptr` must point to an allocated memory block returned by
///      `Self::{allocate, reallocate}`.
///
#[inline]
pub(crate) unsafe fn used_block_hdr_for_allocation_unknown_align(
    ptr: NonNull<u8>,
) -> Option<NonNull<UsedBlockHdr>> {
    // Case 1: `align >= GRANULARITY`
    let c1_block_hdr_ptr: *const NonNull<UsedBlockHdr> =
        addr_of!((*UsedBlockPad::get_for_allocation(ptr)).block_hdr);
    // Case 2: `align < GRANULARITY`
    let c2_block_hdr = ptr.cast::<UsedBlockHdr>().as_ptr().wrapping_sub(1);
    let c2_prev_phys_block_ptr: *const Option<NonNull<BlockHdr>> =
        addr_of!((*c2_block_hdr).common.prev_phys_block);

    // They are both present at the same location, so we can be assured that
    // their contents are initialized and we can read them safely without
    // knowing which case applies first.
    debug_assert_eq!(
        c1_block_hdr_ptr as *const usize,
        c2_prev_phys_block_ptr as *const usize
    );

    // Read it as `Option<NonNull<BlockHdr>>`.
    let block_hdr = if let Some(block_ptr) = *c2_prev_phys_block_ptr {
        // Where does the block represented by `block_ptr` end?
        // (Note: `block_ptr.size` might include `SIZE_USED`.)
        let block_end = block_ptr.as_ptr() as usize + block_ptr.as_ref().size;

        if ptr.as_ptr() as usize > block_end {
            // The block represented by `block_ptr` does not include `ptr`.
            // It's Case 2.
            NonNull::new_unchecked(c2_block_hdr)
        } else {
            // `ptr` is inside the block - it's Case 1.
            // (Note: `ptr == block_end` should count as being inside
            // because the payload might be zero-sized.)
            *c1_block_hdr_ptr
        }
    } else {
        // It's non-nullable in Case 1, so we can rule out Case 1.
        NonNull::new_unchecked(c2_block_hdr)
    };

    if block_hdr.as_ref().common.size & SIZE_USED == 0
        || block_hdr.as_ref().common.size & SIZE_SENTINEL == SIZE_SENTINEL
    {
        log::warn!("0x{:p} is already freed", ptr.as_ptr());
        return None;
    }

    debug_assert_ne!(block_hdr.as_ref().common.size & SIZE_SIZE_MASK, 0);

    Some(block_hdr)
}

#[inline]
pub(crate) unsafe fn size_of_allocation_in_block(
    ptr: NonNull<u8>,
    block: NonNull<UsedBlockHdr>,
) -> usize {
    let size = block.as_ref().common.size - SIZE_USED;
    debug_assert_eq!(size, block.as_ref().common.size & SIZE_SIZE_MASK);
    debug_assert!(size > 0);

    let block_end = block.as_ptr() as usize + size;
    let payload_start = ptr.as_ptr() as usize;

    debug_assert!(block_end > payload_start);
    block_end - payload_start
}

/// Get the payload size of the allocation. The returned size might be
/// larger than the size specified at the allocation time.
///
/// # Safety
///
///  - `ptr` must denote a memory block previously allocated via `Self`.
///  - The memory block must have been allocated with the same alignment
///    ([`Layout::align`]) as `align`.
///
#[inline]
pub(crate) unsafe fn size_of_allocation(ptr: NonNull<u8>, align: usize) -> Option<usize> {
    let block = used_block_hdr_for_allocation(ptr, align)?;
    Some(size_of_allocation_in_block(ptr, block))
}

/// Get the payload size of the allocation with an unknown alignment. The
/// returned size might be larger than the size specified at the allocation
/// time.
///
/// # Safety
///
///  - `ptr` must denote a memory block previously allocated via `Self`.
///
#[inline]
pub(crate) unsafe fn size_of_allocation_unknown_align(ptr: NonNull<u8>) -> Option<usize> {
    // Safety: `ptr` is a previously allocated memory block.
    //         This is upheld by the caller.
    let block = used_block_hdr_for_allocation_unknown_align(ptr)?;
    Some(size_of_allocation_in_block(ptr, block))
}
