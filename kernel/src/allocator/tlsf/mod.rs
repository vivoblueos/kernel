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

pub mod heap;
pub mod int;

use crate::{
    allocator::block::*,
    support::{nonnull_slice_from_raw_parts, nonnull_slice_len, nonnull_slice_start},
};
use const_default::ConstDefault;
use core::{
    alloc::Layout,
    hint::unreachable_unchecked,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
    ptr::NonNull,
};
use int::BinInteger;

/// The TLSF header (top-level) data structure.
///
/// # Data Structure Overview
///
/// <center>
/// ```svgbob
///   First level
///                                                                       "FLLEN = 8"
///                               ╭─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────╮
///        "fl_bitmap: FLBitmap ="│  0  │  0  │  0  │  1  │  0  │  0  │  0  │  0  │
///                               ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
///                     "min size"│ 2¹¹ │ 2¹⁰ │  2⁹ │  2⁸ │  2⁷ │  2⁶ │  2⁵ │  2⁴ │
///                               ╰─────┴─────┴─────┴──┬──┴─────┴─────┴─────┴─────╯
///                                                    │
/// ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
///   Second Level                                     │
///                                                    v                      "SLLEN = 8"
///                                  ╭─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────╮
///        "sl_bitmap[4]: SLBitmap ="│  0  │  0  │  1  │  0  │  0  │  0  │  0  │  0  │
///                                  ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
///              "min size 2⁸(1+n/8)"│  7  │  6  │  5  │  4  │  3  │  2  │  1  │  0  │
///                                  ├─────┼─────┼─────┼─────┼─────┼─────┼─────┼─────┤
///                      "first_free"│     │     │  ○  │     │     │     │     │     │
///                                  ╰─────┴─────┴──┼──┴─────┴─────┴─────┴─────┴─────╯
///                                                 │
///                                                 │  "size = 416..448"
///                                                 │
/// ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┼ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
///   Free blocks                                   │
///                                                 │
///             ╭───────────────────────────────────╯
///             │ ╭───┬───┬───────╮    ╭───┬───┬───────╮    ╭───┬───┬───────╮
///             ╰─┼>○ │ ○─┼───────┼────┼>○ │ ○─┼───────┼────┼>○ │   │       │
///               ├───┴───╯       │    ├───┴───╯       │    ├───┴───╯       │
///               │               │    │               │    │               │
///               │               │    │               │    │               │
///               ╰───────────────╯    ╰───────────────╯    ╰───────────────╯
///                   416 bytes            432 bytes            416 bytes
/// ```
/// </center>
///
/// # Properties
///
/// The allocation granularity ([`GRANULARITY`]) is `size_of::<usize>() * 4`
/// bytes, which is the minimum size of a free block.
///
/// The maximum block size is `(GRANULARITY << FLLEN) - GRANULARITY`.
///
#[derive(Debug)]
pub struct Tlsf<'pool, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> {
    fl_bitmap: FLBitmap,
    /// `sl_bitmap[fl].get_bit(sl)` is set if `first_free[fl][sl].is_some()`
    sl_bitmap: [SLBitmap; FLLEN],
    first_free: [[Option<NonNull<FreeBlockHdr>>; SLLEN]; FLLEN],
    allocated: usize,
    maximum: usize,
    total: usize,
    _phantom: PhantomData<&'pool ()>,
}

// Safety: All memory block headers directly or indirectly referenced by a
//         particular instance of `Tlsf` are logically owned by that `Tlsf` and
//         have no interior mutability, so these are safe.
unsafe impl<FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> Send
    for Tlsf<'_, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
}

unsafe impl<FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> Sync
    for Tlsf<'_, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
}

/// The header of a free memory block.
#[repr(C)]
#[cfg_attr(target_pointer_width = "16", repr(align(8)))]
#[cfg_attr(target_pointer_width = "32", repr(align(16)))]
#[cfg_attr(target_pointer_width = "64", repr(align(32)))]
#[derive(Debug)]
struct FreeBlockHdr {
    common: BlockHdr,
    next_free: Option<NonNull<FreeBlockHdr>>,
    prev_free: Option<NonNull<FreeBlockHdr>>,
}

impl<FLBitmap: BinInteger, SLBitmap: BinInteger, const FLLEN: usize, const SLLEN: usize> Default
    for Tlsf<'_, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<FLBitmap: BinInteger, SLBitmap: BinInteger, const FLLEN: usize, const SLLEN: usize>
    ConstDefault for Tlsf<'_, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    const DEFAULT: Self = Self::new();
}

impl<'pool, FLBitmap: BinInteger, SLBitmap: BinInteger, const FLLEN: usize, const SLLEN: usize>
    Tlsf<'pool, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    /// Construct an empty pool.
    #[inline]
    pub const fn new() -> Self {
        Self {
            fl_bitmap: FLBitmap::ZERO,
            sl_bitmap: [SLBitmap::ZERO; FLLEN],
            first_free: [[None; SLLEN]; FLLEN],
            _phantom: {
                let () = Self::VALID;
                PhantomData
            },
            allocated: 0,
            maximum: 0,
            total: 0,
        }
    }

    // For testing
    const FLLEN: usize = FLLEN;
    const SLLEN: usize = SLLEN;

    /// Evaluates successfully only if the parameters are valid.
    const VALID: () = {
        if FLLEN == 0 {
            panic!("`FLLEN` must not be zero");
        }
        if SLLEN == 0 {
            panic!("`SLLEN` must not be zero");
        }
        if (FLBitmap::BITS as u128) < FLLEN as u128 {
            panic!("`FLBitmap` should contain at least `FLLEN` bits");
        }
        if (SLBitmap::BITS as u128) < SLLEN as u128 {
            panic!("`SLBitmap` should contain at least `SLLEN` bits");
        }
    };

    /// The maximum size of each memory pool region. This is constrained by
    /// the maximum block size of the segregated list to contain the initial
    /// free memory block.
    const MAX_POOL_SIZE: Option<usize> = {
        let shift = GRANULARITY_LOG2 + FLLEN as u32;
        if shift < usize::BITS {
            Some(1 << shift)
        } else {
            None
        }
    };

    /// `SLLEN.log2()`
    const SLI: u32 = if SLLEN.is_power_of_two() {
        SLLEN.trailing_zeros()
    } else {
        panic!("`SLLEN` is not power of two")
    };

    /// Find the free block list to store a free block of the specified size.
    #[inline]
    fn map_floor(size: usize) -> Option<(usize, usize)> {
        debug_assert!(size >= GRANULARITY);
        debug_assert!(size % GRANULARITY == 0);
        let fl = usize::BITS - GRANULARITY_LOG2 - 1 - size.leading_zeros();

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching. Underflowed digits can be simply masked out
        // in `map_floor`.
        let sl = size.rotate_right((fl + GRANULARITY_LOG2).wrapping_sub(Self::SLI));

        // The most significant one of `size` should be now at `sl[SLI]`
        debug_assert!(((sl >> Self::SLI) & 1) == 1);

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    /// Find the first free block list whose every item is at least as large
    /// as the specified size.
    #[inline]
    fn map_ceil(size: usize) -> Option<(usize, usize)> {
        debug_assert!(size >= GRANULARITY);
        debug_assert!(size % GRANULARITY == 0);
        let mut fl = usize::BITS - GRANULARITY_LOG2 - 1 - size.leading_zeros();

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        let mut sl = size.rotate_right((fl + GRANULARITY_LOG2).wrapping_sub(Self::SLI));

        // The most significant one of `size` should be now at `sl[SLI]`
        debug_assert!(((sl >> Self::SLI) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        sl = (sl & (SLLEN - 1)) + (sl >= (1 << (Self::SLI + 1))) as usize;

        // if sl[SLI] { fl += 1; sl = 0; }
        fl += (sl >> Self::SLI) as u32;

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    const MAX_MAP_CEIL_AND_UNMAP_INPUT: usize = {
        // The maximum value for which `map_ceil(x)` returns `(usize::BITS -
        // GRANULARITY_LOG2 - 1, _)`, assuming `FLLEN == ∞`
        let max1 = !(usize::MAX >> (Self::SLI + 1));

        // Now take into account the fact that `FLLEN` is not actually infinity
        if FLLEN as u32 - 1 < usize::BITS - GRANULARITY_LOG2 - 1 {
            max1 >> ((usize::BITS - GRANULARITY_LOG2 - 1) - (FLLEN as u32 - 1))
        } else {
            max1
        }
    };

    /// Find the first free block list whose every item is at least as large
    /// as the specified size and get the list's minimum size. Returns `None`
    /// if there isn't such a list, or the list's minimum size is not
    /// representable in `usize`.
    #[inline]
    fn map_ceil_and_unmap(size: usize) -> Option<usize> {
        debug_assert!(size >= GRANULARITY);
        debug_assert!(size % GRANULARITY == 0);

        if size > Self::MAX_MAP_CEIL_AND_UNMAP_INPUT {
            return None;
        }

        let fl = usize::BITS - GRANULARITY_LOG2 - 1 - size.leading_zeros();

        let list_min_size = if GRANULARITY_LOG2 < Self::SLI && fl < Self::SLI - GRANULARITY_LOG2 {
            size
        } else {
            let shift = fl + GRANULARITY_LOG2 - Self::SLI;

            // round up
            (size + ((1 << shift) - 1)) & !((1 << shift) - 1)
        };

        Some(list_min_size)
    }

    /// Insert the specified free block to the corresponding free block list.
    ///
    /// Updates `FreeBlockHdr::{prev_free, next_free}`.
    ///
    /// # Safety
    ///
    ///  - `*block.as_ptr()` must be owned by `self`. (It does not have to be
    ///    initialized, however.)
    ///  - `size` must have a corresponding free list, which does not currently
    ///    contain `block`.
    ///
    #[cfg_attr(target_arch = "wasm32", inline(never))]
    unsafe fn link_free_block(&mut self, mut block: NonNull<FreeBlockHdr>, size: usize) {
        let (fl, sl) = Self::map_floor(size).unwrap_or_else(|| {
            debug_assert!(false, "could not map size {}", size);
            // Safety: It's unreachable
            unreachable_unchecked()
        });
        let first_free = &mut self.first_free[fl][sl];
        let next_free = mem::replace(first_free, Some(block));
        block.as_mut().next_free = next_free;
        block.as_mut().prev_free = None;
        if let Some(mut next_free) = next_free {
            next_free.as_mut().prev_free = Some(block);
        }

        self.fl_bitmap.set_bit(fl as u32);
        self.sl_bitmap[fl].set_bit(sl as u32);
    }

    /// Remove the specified free block from the corresponding free block list.
    ///
    /// # Safety
    ///
    ///  - `size` must represent the specified free block's size.
    ///  - The free block must be currently included in a free block list.
    ///
    #[cfg_attr(target_arch = "wasm32", inline(never))]
    unsafe fn unlink_free_block(&mut self, mut block: NonNull<FreeBlockHdr>, size: usize) {
        let next_free = block.as_mut().next_free;
        let prev_free = block.as_mut().prev_free;

        if let Some(mut next_free) = next_free {
            next_free.as_mut().prev_free = prev_free;
        }

        if let Some(mut prev_free) = prev_free {
            prev_free.as_mut().next_free = next_free;
        } else {
            let (fl, sl) = Self::map_floor(size).unwrap_or_else(|| {
                debug_assert!(false, "could not map size {}", size);
                // Safety: It's unreachable
                unreachable_unchecked()
            });
            let first_free = &mut self.first_free[fl][sl];

            debug_assert_eq!(*first_free, Some(block));
            *first_free = next_free;

            if next_free.is_none() {
                // The free list is now empty - update the bitmap
                self.sl_bitmap[fl].clear_bit(sl as u32);
                if self.sl_bitmap[fl] == SLBitmap::ZERO {
                    self.fl_bitmap.clear_bit(fl as u32);
                }
            }
        }
    }

    /// Create a new memory pool at the location specified by a slice pointer.
    ///
    /// Returns the actual number of bytes (counted from the beginning of
    /// `block`) used to create the memory pool. This value is necessary to
    /// calculate the start address to pass to [`Self::append_free_block_ptr`].
    ///
    /// This method does nothing and returns `None` if the given memory block is
    /// too small.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in linear time (`O(block.len())`) because
    /// it might need to divide the memory block to meet the maximum block size
    /// requirement (`(GRANULARITY << FLLEN) - GRANULARITY`).
    ///
    /// # Examples
    ///
    /// ```
    /// use rlsf::Tlsf;
    /// use std::{mem::MaybeUninit, ptr::NonNull};
    /// static mut POOL: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
    /// let mut tlsf: Tlsf<u8, u8, 8, 8> = Tlsf::new();
    /// unsafe {
    ///     tlsf.insert_free_block_ptr(NonNull::new(POOL.as_mut_ptr()).unwrap());
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The memory block will be considered owned by `self`. The memory block
    /// must outlive `self`.
    ///
    /// # Panics
    ///
    /// This method never panics.
    pub unsafe fn insert_free_block_ptr(&mut self, block: NonNull<[u8]>) -> Option<NonZeroUsize> {
        let len = nonnull_slice_len(block);

        // Round up the starting address
        let unaligned_start = block.as_ptr() as *mut u8 as usize;
        let start = unaligned_start.wrapping_add(GRANULARITY - 1) & !(GRANULARITY - 1);

        let len = if let Some(x) = len
            .checked_sub(start.wrapping_sub(unaligned_start))
            .filter(|&x| x >= GRANULARITY * 2)
        {
            // Round down
            x & !(GRANULARITY - 1)
        } else {
            // The block is too small
            return None;
        };

        // Safety: The slice being created here
        let pool_len = self.insert_free_block_ptr_aligned(NonNull::new_unchecked(
            core::ptr::slice_from_raw_parts_mut(start as *mut u8, len),
        ))?;

        // Safety: The sum should not wrap around because it represents the size
        //         of a memory pool on memory
        Some(NonZeroUsize::new_unchecked(
            pool_len.get() + start.wrapping_sub(unaligned_start),
        ))
    }

    /// [`insert_free_block_ptr`] with a well-aligned slice passed by `block`.
    pub(crate) unsafe fn insert_free_block_ptr_aligned(
        &mut self,
        block: NonNull<[u8]>,
    ) -> Option<NonZeroUsize> {
        let start = block.as_ptr() as *mut u8 as usize;
        let mut size = nonnull_slice_len(block);

        let mut cursor = start;

        while size >= GRANULARITY * 2 {
            let chunk_size = if let Some(max_pool_size) = Self::MAX_POOL_SIZE {
                size.min(max_pool_size)
            } else {
                size
            };

            debug_assert_eq!(chunk_size % GRANULARITY, 0);

            // The new free block
            // Safety: `cursor` is not zero.
            let mut block = NonNull::new_unchecked(cursor as *mut FreeBlockHdr);

            // Initialize the new free block
            block.as_mut().common = BlockHdr::new(chunk_size - GRANULARITY, None);

            // Cap the end with a sentinel block (a permanently-used block)
            let mut sentinel_block = block
                .as_ref()
                .common
                .next_phys_block()
                .cast::<UsedBlockHdr>();

            sentinel_block.as_mut().common =
                BlockHdr::new(GRANULARITY | SIZE_USED | SIZE_SENTINEL, Some(block.cast()));

            // Link the free block to the corresponding free list
            self.link_free_block(block, chunk_size - GRANULARITY);

            // `cursor` can reach `usize::MAX + 1`, but in such a case, this
            // iteration must be the last one
            debug_assert!(cursor.checked_add(chunk_size).is_some() || size == chunk_size);
            size -= chunk_size;
            cursor = cursor.wrapping_add(chunk_size);
        }

        let pool_len = cursor.wrapping_sub(start);
        self.total += pool_len;

        NonZeroUsize::new(pool_len)
    }

    /// Extend an existing memory pool by incorporating the specified memory
    /// block.
    ///
    /// Returns the number of incorporated bytes, counted from the beginning of
    /// `block`.
    ///
    /// In the current implementation, this method can coalesce memory pools
    /// only if the maximum pool size is outside the range of `usize`, i.e.,
    /// `log2(GRANULARITY) + FLLEN >= usize::BITS`. This is because it does not
    /// track each pool's size and cannot check whether the resulting pool will
    /// have a valid size.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in linear time (`O(block.len())`) because
    /// it might need to divide the memory block to meet the maximum block size
    /// requirement (`(GRANULARITY << FLLEN) - GRANULARITY`).
    ///
    /// # Examples
    ///
    /// ```
    /// use rlsf::Tlsf;
    /// use std::{mem::MaybeUninit, ptr::NonNull};
    ///
    /// static mut POOL: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
    /// let mut cursor = unsafe { POOL.as_mut_ptr() } as *mut u8;
    /// let mut remaining_len = 1024;
    ///
    /// let mut tlsf: Tlsf<u8, u8, 8, 8> = Tlsf::new();
    /// let pool0_len = unsafe {
    ///     tlsf.insert_free_block_ptr(nonnull_slice_from_raw_parts(
    ///         NonNull::new(cursor).unwrap(), remaining_len / 2))
    /// }.unwrap().get();
    /// cursor = cursor.wrapping_add(pool0_len);
    /// remaining_len -= pool0_len;
    ///
    /// let pool1_len = unsafe {
    ///     tlsf.append_free_block_ptr(nonnull_slice_from_raw_parts(
    ///         NonNull::new(cursor).unwrap(), remaining_len / 2))
    /// };
    /// cursor = cursor.wrapping_add(pool1_len);
    /// remaining_len -= pool1_len;
    ///
    /// let pool2_len = unsafe {
    ///     tlsf.append_free_block_ptr(nonnull_slice_from_raw_parts(
    ///         NonNull::new(cursor).unwrap(), remaining_len))
    /// };
    /// cursor = cursor.wrapping_add(pool2_len);
    /// remaining_len -= pool2_len;
    ///
    /// // polyfill for <https://github.com/rust-lang/rust/issues/71941>
    /// fn nonnull_slice_from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> NonNull<[T]> {
    ///     NonNull::new(std::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len)).unwrap()
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The memory block will be considered owned by `self`. The memory block
    /// must outlive `self`.
    ///
    /// `block`'s starting address must match an existing memory pool's
    /// ending address. See the above example for how to obtain one.
    ///
    /// # Panics
    ///
    /// This method never panics.
    pub unsafe fn append_free_block_ptr(&mut self, block: NonNull<[u8]>) -> usize {
        // Round down the length
        let start = nonnull_slice_start(block);
        let len = nonnull_slice_len(block) & !(GRANULARITY - 1);

        if Self::MAX_POOL_SIZE.is_some() {
            // If `MAX_POOL_SIZE` is `Some(_)`, it's dangerous to coalesce
            // memory pools of unknown sizes, so fall back to calling
            // `insert_free_block_ptr_aligned`.
            let block = nonnull_slice_from_raw_parts(start, len);
            return self
                .insert_free_block_ptr_aligned(block)
                .map(NonZeroUsize::get)
                .unwrap_or(0);
        } else if len == 0 {
            // `block` is so short that the `insert_free_block_ptr` will not
            // even create a sentinel block. We'll corrupt the structure if we
            // proceed.
            return 0;
        }

        let original_start = start.as_ptr();
        let mut start = original_start;
        let end = (start as usize).wrapping_add(len);

        // The sentinel block from the preceding memory pool will be
        // assimilated into `[start..end]`.
        start = start.wrapping_sub(GRANULARITY);
        let sentinel_block = start as *mut UsedBlockHdr;
        debug_assert_eq!(
            (*sentinel_block).common.size,
            GRANULARITY | SIZE_USED | SIZE_SENTINEL
        );

        // The adjacent free block (if there's one) from the preceding memory
        // pool will be assimilated into `[start..end]`.
        let penultimate_block = (*sentinel_block).common.prev_phys_block.unwrap_or_else(|| {
            debug_assert!(false, "sentinel block has no `prev_phys_block`");
            // Safety: It's unreachable
            unreachable_unchecked()
        });
        let last_nonassimilated_block;
        if (penultimate_block.as_ref().size & SIZE_USED) == 0 {
            let free_block = penultimate_block.cast::<FreeBlockHdr>();
            let free_block_size = free_block.as_ref().common.size;
            debug_assert_eq!(
                free_block_size,
                free_block.as_ref().common.size & SIZE_SIZE_MASK
            );
            self.unlink_free_block(free_block, free_block_size);

            // Assimilation success
            start = free_block.as_ptr() as *mut u8;
            last_nonassimilated_block = free_block.as_ref().common.prev_phys_block;
        } else {
            // Assimilation failed
            last_nonassimilated_block = Some(penultimate_block);
        }

        // Safety: `start` points to a location inside an existion memory pool,
        //         so it's non-null
        let block = nonnull_slice_from_raw_parts(
            NonNull::new_unchecked(start),
            end.wrapping_sub(start as usize),
        );

        // Create a memory pool
        let pool_len = self
            .insert_free_block_ptr_aligned(block)
            .unwrap_or_else(|| {
                debug_assert!(false, "`pool_size_to_contain_allocation` is an impostor");
                // Safety: It's unreachable
                unreachable_unchecked()
            })
            .get();

        // Link the created pool's first block to the preceding memory pool's
        // last non-assimilated block to form one continuous memory pool
        let mut first_block = nonnull_slice_start(block).cast::<FreeBlockHdr>();
        first_block.as_mut().common.prev_phys_block = last_nonassimilated_block;

        // Exclude the assimilated part from the returned value
        pool_len - (original_start as usize).wrapping_sub(start as usize)
    }

    /// Create a new memory pool at the location specified by a slice.
    ///
    /// This method does nothing if the given memory block is too small.
    ///
    /// (The return type is yet to be determined.)
    ///
    /// # Time Complexity
    ///
    /// See [`Self::insert_free_block_ptr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rlsf::Tlsf;
    /// use std::mem::MaybeUninit;
    /// let mut pool = [MaybeUninit::uninit(); 1024];
    /// let mut tlsf: Tlsf<u8, u8, 8, 8> = Tlsf::new();
    /// tlsf.insert_free_block(&mut pool);
    /// ```
    ///
    /// The insertred memory block must outlive `self`:
    ///
    /// ```rust,compile_fail
    /// use rlsf::Tlsf;
    /// use std::mem::MaybeUninit;
    /// let mut tlsf: Tlsf<u8, u8, 8, 8> = Tlsf::new();
    /// let mut pool = [MaybeUninit::uninit(); 1024];
    /// tlsf.insert_free_block(&mut pool);
    /// drop(pool); // dropping the memory block first is not allowed
    /// drop(tlsf);
    /// ```
    ///
    /// # Panics
    ///
    /// This method never panics.
    #[inline]
    pub fn insert_free_block(&mut self, block: &'pool mut [MaybeUninit<u8>]) -> impl Send + Sync {
        // Safety: `block` is a mutable reference, which guarantees the absence
        // of aliasing references. Being `'pool` means it will outlive `self`.
        unsafe { self.insert_free_block_ptr(NonNull::new(block as *mut [_] as _).unwrap()) };
    }

    /// Calculate the minimum size of a `GRANULARITY`-byte aligned memory pool
    /// (a well-aligned free memory block to be passed to
    /// [`Self::insert_free_block`]) that is guaranteed to be able to contain
    /// the specified allocation.
    ///
    /// Returns `None` if no amount of additional memory space can make the
    /// allocation containable.
    #[inline]
    pub(crate) fn pool_size_to_contain_allocation(layout: Layout) -> Option<usize> {
        // The extra bytes consumed by the header and padding. See
        // `Tlsf::allocate` for details.
        let max_overhead =
            layout.align().saturating_sub(GRANULARITY / 2) + mem::size_of::<UsedBlockHdr>();

        // Which segregated list we would look if we were allocating this?
        // And what's the minimum size of a free block required for inclusion
        // in this list?
        let search_size = layout.size().checked_add(max_overhead)?;
        let search_size = search_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
        let list_min_size = Self::map_ceil_and_unmap(search_size)?;

        // Add the sentinel block size
        list_min_size.checked_add(GRANULARITY)
    }

    /// Attempt to allocate a block of memory.
    ///
    /// Returns the starting address of the allocated memory block on success;
    /// `None` otherwise.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time.
    pub fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        unsafe {
            let (max_overhead, search_size) = get_overhead_and_size(layout)?;
            let (fl, sl) = self.search_suitable_free_block_list_for_allocation(search_size)?;

            // Get a free block: `block`
            let first_free = self.first_free.get_unchecked_mut(fl).get_unchecked_mut(sl);
            let block = first_free.unwrap_or_else(|| {
                debug_assert!(false, "bitmap outdated");
                // Safety: It's unreachable
                unreachable_unchecked()
            });

            let mut next_phys_block = block.as_ref().common.next_phys_block();
            let size_and_flags = block.as_ref().common.size;
            let size = size_and_flags /* size_and_flags & SIZE_SIZE_MASK */;
            debug_assert_eq!(size, size_and_flags & SIZE_SIZE_MASK);

            debug_assert!(size >= search_size);

            // Unlink the free block. We are not using `unlink_free_block` because
            // we already know `(fl, sl)` and that `block.prev_free` is `None`.
            *first_free = block.as_ref().next_free;
            if let Some(mut next_free) = *first_free {
                next_free.as_mut().prev_free = None;
            } else {
                // The free list is now empty - update the bitmap
                let sl_bitmap = self.sl_bitmap.get_unchecked_mut(fl);
                sl_bitmap.clear_bit(sl as u32);
                if *sl_bitmap == SLBitmap::ZERO {
                    self.fl_bitmap.clear_bit(fl as u32);
                }
            }

            // Decide the starting address of the payload
            let unaligned_ptr = block.as_ptr() as *mut u8 as usize + mem::size_of::<UsedBlockHdr>();
            let ptr = NonNull::new_unchecked(
                (unaligned_ptr.wrapping_add(layout.align() - 1) & !(layout.align() - 1)) as *mut u8,
            );

            if layout.align() < GRANULARITY {
                debug_assert_eq!(unaligned_ptr, ptr.as_ptr() as usize);
            } else {
                debug_assert_ne!(unaligned_ptr, ptr.as_ptr() as usize);
            }

            // Calculate the actual overhead and the final block size of the
            // used block being created here
            let overhead = ptr.as_ptr() as usize - block.as_ptr() as usize;
            debug_assert!(overhead <= max_overhead);

            let new_size = overhead + layout.size();
            let new_size = (new_size + GRANULARITY - 1) & !(GRANULARITY - 1);
            debug_assert!(new_size <= search_size);

            let new_size = if new_size == size {
                // The allocation completely fills this free block.
                // Updating `next_phys_block.prev_phys_block` is unnecessary in this
                // case because it's still supposed to point to `block`.
                new_size
            } else {
                // The allocation partially fills this free block. Create a new
                // free block header at `block + new_size..block + size`
                // of length (`new_free_block_size`).
                let mut new_free_block: NonNull<FreeBlockHdr> =
                    NonNull::new_unchecked(block.cast::<u8>().as_ptr().add(new_size)).cast();
                let new_free_block_size = size - new_size;

                if new_free_block_size >= GRANULARITY {
                    // Update `next_phys_block.prev_phys_block` to point to this new
                    // free block
                    // Invariant: No two adjacent free blocks
                    debug_assert!((next_phys_block.as_ref().size & SIZE_USED) != 0);
                    next_phys_block.as_mut().prev_phys_block = Some(new_free_block.cast());

                    // Create the new free block header
                    new_free_block.as_mut().common =
                        BlockHdr::new(new_free_block_size, Some(block.cast()));
                    self.link_free_block(new_free_block, new_free_block_size);
                    new_size
                } else {
                    size
                }
            };

            // Turn `block` into a used memory block and initialize the used block
            // header. `prev_phys_block` is already set.
            let mut block = block.cast::<UsedBlockHdr>();
            block.as_mut().common.size = new_size | SIZE_USED;

            // Place a `UsedBlockPad` (used by `used_block_hdr_for_allocation`)
            if layout.align() >= GRANULARITY {
                (*UsedBlockPad::get_for_allocation(ptr)).block_hdr = block;
            }

            self.allocated += new_size;
            self.maximum = core::cmp::max(self.maximum, self.allocated);

            Some(ptr)
        }
    }

    /// Search for a non-empty free block list for allocation.
    #[inline]
    fn search_suitable_free_block_list_for_allocation(
        &self,
        min_size: usize,
    ) -> Option<(usize, usize)> {
        let (mut fl, mut sl) = Self::map_ceil(min_size)?;

        // Search in range `(fl, sl..SLLEN)`
        sl = self.sl_bitmap[fl].bit_scan_forward(sl as u32) as usize;
        if sl < SLLEN {
            debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));

            return Some((fl, sl));
        }

        // Search in range `(fl + 1.., ..)`
        fl = self.fl_bitmap.bit_scan_forward(fl as u32 + 1) as usize;
        if fl < FLLEN {
            debug_assert!(self.fl_bitmap.get_bit(fl as u32));

            sl = self.sl_bitmap[fl].trailing_zeros() as usize;
            if sl >= SLLEN {
                debug_assert!(false, "bitmap contradiction");
                unsafe { unreachable_unchecked() };
            }

            debug_assert!(self.sl_bitmap[fl].get_bit(sl as u32));
            Some((fl, sl))
        } else {
            None
        }
    }

    /// Deallocate a previously allocated memory block.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///  - The memory block must have been allocated with the same alignment
    ///    ([`Layout::align`]) as `align`.
    ///
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, align: usize) -> usize {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let Some(block) = used_block_hdr_for_allocation(ptr, align) else {
            return 0;
        };
        let block = block.cast::<BlockHdr>();
        self.deallocate_block(block)
    }

    /// Deallocate a previously allocated memory block with an unknown alignment.
    ///
    /// Unlike `deallocate`, this function does not require knowing the
    /// allocation's alignment but might be less efficient.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///
    pub(crate) unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) -> usize {
        // Safety: `ptr` is a previously allocated memory block. This is upheld
        //         by the caller.
        let Some(block) = used_block_hdr_for_allocation_unknown_align(ptr) else {
            return 0;
        };
        let block = block.cast::<BlockHdr>();
        self.deallocate_block(block)
    }

    /// Deallocate a previously allocated memory block. Takes a pointer to
    /// `BlockHdr` instead of a payload pointer.
    #[inline]
    pub(crate) unsafe fn deallocate_block(&mut self, mut block: NonNull<BlockHdr>) -> usize {
        let deallocated_size = block.as_ref().size & !SIZE_USED;
        debug_assert!((block.as_ref().size & SIZE_USED) != 0);
        self.allocated -= deallocated_size;
        let mut size = deallocated_size;

        // This variable tracks whose `prev_phys_block` we should update.
        let mut new_next_phys_block;

        // Merge the created hole with the next block if the next block is a
        // free block
        // Safety: `block.common` should be fully up-to-date and valid
        let next_phys_block = block.as_ref().next_phys_block();
        let next_phys_block_size_and_flags = next_phys_block.as_ref().size;
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            let next_phys_block_size = next_phys_block_size_and_flags;
            debug_assert_eq!(
                next_phys_block_size_and_flags & SIZE_SIZE_MASK,
                next_phys_block_size
            );

            // It's coalescable. Add its size to `size`. This will transfer
            // any `SIZE_LAST_IN_POOL` flag `next_phys_block` may have at
            // the same time.
            size += next_phys_block_size;

            // Safety: `next_phys_block` is a free block and therefore is not a
            // sentinel block
            new_next_phys_block = next_phys_block.as_ref().next_phys_block();

            // Unlink `next_phys_block`.
            self.unlink_free_block(next_phys_block.cast(), next_phys_block_size);
        } else {
            new_next_phys_block = next_phys_block;
        }

        // Merge with the previous block if it's a free block.
        if let Some(prev_phys_block) = block.as_ref().prev_phys_block {
            let prev_phys_block_size_and_flags = prev_phys_block.as_ref().size;

            if (prev_phys_block_size_and_flags & SIZE_USED) == 0 {
                let prev_phys_block_size = prev_phys_block_size_and_flags;
                debug_assert_eq!(
                    prev_phys_block_size_and_flags & SIZE_SIZE_MASK,
                    prev_phys_block_size
                );

                // It's coalescable. Add its size to `size`.
                size += prev_phys_block_size;

                // Unlink `prev_phys_block`.
                self.unlink_free_block(prev_phys_block.cast(), prev_phys_block_size);

                // Move `block` to where `prev_phys_block` is located. By doing
                // this, `block` will implicitly inherit `prev_phys_block.
                // as_ref().prev_phys_block`.
                block = prev_phys_block;
            }
        }

        // Write the new free block's size and flags.
        debug_assert!((size & SIZE_USED) == 0);
        block.as_mut().size = size;

        // Link this free block to the corresponding free list
        let block = block.cast::<FreeBlockHdr>();
        self.link_free_block(block, size);

        // Link `new_next_phys_block.prev_phys_block` to `block`
        debug_assert_eq!(new_next_phys_block, block.as_ref().common.next_phys_block());
        new_next_phys_block.as_mut().prev_phys_block = Some(block.cast());
        deallocated_size
    }

    // TODO: `reallocate_no_move` (constant-time reallocation)

    /// Shrink or grow a previously allocated memory block.
    ///
    /// Returns the new starting address of the memory block on success;
    /// `None` otherwise.
    ///
    /// # Time Complexity
    ///
    /// Unlike other methods, this method will complete in linear time
    /// (`O(old_size)`).
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///  - The memory block must have been allocated with the same alignment
    ///    ([`Layout::align`]) as `new_layout`.
    ///
    pub unsafe fn reallocate(
        &mut self,
        ptr: NonNull<u8>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let block = used_block_hdr_for_allocation(ptr, new_layout.align())?;

        // Do this early so that the compiler can de-duplicate common
        // subexpressions such as `block.as_ref().common.size - SIZE_USED`
        let old_size = size_of_allocation_in_block(ptr, block);

        // First try to shrink or grow the block in-place (i.e., without
        // allocating a whole new memory block).
        if let Some(x) = self.reallocate_inplace(ptr, block, new_layout) {
            return Some(x);
        }

        // Allocate a whole new memory block
        let new_ptr = self.allocate(new_layout)?;

        // Move the existing data into the new location
        debug_assert!(new_layout.size() >= old_size);
        core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);

        // Deallocate the old memory block.
        self.deallocate(ptr, new_layout.align());

        Some(new_ptr)
    }

    pub unsafe fn reallocate_unknown_align(
        &mut self,
        ptr: NonNull<u8>,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let block = used_block_hdr_for_allocation_unknown_align(ptr)?;

        // Do this early so that the compiler can de-duplicate common
        // subexpressions such as `block.as_ref().common.size - SIZE_USED`
        let old_size = size_of_allocation_in_block(ptr, block);

        let new_layout = Layout::from_size_align_unchecked(new_size, mem::size_of::<usize>());
        // First try to shrink or grow the block in-place (i.e., without
        // allocating a whole new memory block).
        if let Some(x) = self.reallocate_inplace(ptr, block, &new_layout) {
            return Some(x);
        }

        // Allocate a whole new memory block
        let new_ptr = self.allocate(&new_layout)?;

        // Move the existing data into the new location
        debug_assert!(new_layout.size() >= old_size);
        core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);

        // Deallocate the old memory block.
        self.deallocate(ptr, new_layout.align());

        Some(new_ptr)
    }

    /// A subroutine of [`Self::reallocate`] that tries to reallocate a memory
    /// block in-place.
    #[inline]
    unsafe fn reallocate_inplace(
        &mut self,
        ptr: NonNull<u8>,
        mut block: NonNull<UsedBlockHdr>,
        new_layout: &Layout,
    ) -> Option<NonNull<u8>> {
        // The extra bytes consumed by the header and any padding
        let overhead = ptr.as_ptr() as usize - block.as_ptr() as usize;

        // Calculate the new block size. Fail if this causes an overflow.
        // Failing at this point does not necessarily mean the whole process of
        // reallocation has failed; a new place with a smaller overhead could be
        // found later (whether there's actually such a situation or not is yet
        // to be proven).
        let new_size = overhead.checked_add(new_layout.size())?;
        let new_size = new_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);

        let old_size = block.as_ref().common.size - SIZE_USED;
        debug_assert_eq!(old_size, block.as_ref().common.size & SIZE_SIZE_MASK);

        // Shrinking
        // ------------------------------------------------------------------

        if new_size <= old_size {
            if new_size == old_size {
                // No size change
            } else {
                // Shrink the block, creating a new free block at the end
                let shrink_by = old_size - new_size;

                // We will create a new free block at this address
                let mut new_free_block: NonNull<FreeBlockHdr> =
                    NonNull::new_unchecked(block.cast::<u8>().as_ptr().add(new_size)).cast();
                let mut new_free_block_size = shrink_by;

                // If the next block is a free block...
                let mut next_phys_block = block.as_ref().common.next_phys_block();
                let next_phys_block_size_and_flags = next_phys_block.as_ref().size;
                if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
                    let next_phys_block_size = next_phys_block_size_and_flags;
                    debug_assert_eq!(
                        next_phys_block_size,
                        next_phys_block_size_and_flags & SIZE_SIZE_MASK
                    );

                    // Then we can merge this existing free block (`next_phys_block`)
                    // into the new one (`new_free_block`).
                    self.unlink_free_block(next_phys_block.cast(), next_phys_block_size);
                    new_free_block_size += next_phys_block_size;

                    let mut next_next_phys_block = next_phys_block.as_ref().next_phys_block();
                    next_next_phys_block.as_mut().prev_phys_block = Some(new_free_block.cast());
                } else {
                    // We can't merge a used block (`next_phys_block`) and
                    // a free block (`new_free_block`).
                    next_phys_block.as_mut().prev_phys_block = Some(new_free_block.cast());
                }

                new_free_block.as_mut().common =
                    BlockHdr::new(new_free_block_size, Some(block.cast()));
                self.link_free_block(new_free_block, new_free_block_size);

                block.as_mut().common.size = new_size | SIZE_USED;
            }

            return Some(ptr);
        }

        // In-place non-moving reallocation
        // ------------------------------------------------------------------

        debug_assert!(new_size > old_size);

        let grow_by = new_size - old_size;
        let next_phys_block = block.as_ref().common.next_phys_block();

        // If we removed this block, there would be a continous free space of
        // `moving_clearance` bytes, which is followed by `moving_clearance_end`
        let mut moving_clearance = old_size;
        let mut moving_clearance_end = next_phys_block;

        // Grow into the next free block. Fail if there isn't such a block.
        #[allow(clippy::never_loop)]
        'nonmoving: loop {
            let next_phys_block_size_and_flags = next_phys_block.as_ref().size;

            // Fail it isn't a free block.
            if (next_phys_block_size_and_flags & SIZE_USED) != 0 {
                break 'nonmoving;
            }

            let mut next_phys_block_size = next_phys_block_size_and_flags;
            debug_assert_eq!(
                next_phys_block_size,
                next_phys_block_size_and_flags & SIZE_SIZE_MASK
            );

            // Now we know it's really a free block.
            let mut next_phys_block = next_phys_block.cast::<FreeBlockHdr>();
            let mut next_next_phys_block = next_phys_block.as_ref().common.next_phys_block();

            moving_clearance += next_phys_block_size;
            moving_clearance_end = next_next_phys_block;

            if grow_by > next_phys_block_size {
                // Can't fit
                break 'nonmoving;
            }

            self.unlink_free_block(next_phys_block, next_phys_block_size);

            if grow_by < next_phys_block_size {
                // Can fit and there's some slack. Create a free block to fill
                // the slack.
                next_phys_block_size -= grow_by;

                next_phys_block =
                    NonNull::new_unchecked(block.cast::<u8>().as_ptr().add(new_size)).cast();
                next_phys_block.as_mut().common =
                    BlockHdr::new(next_phys_block_size, Some(block.cast()));
                self.link_free_block(next_phys_block, next_phys_block_size);

                // Update `next_next_phys_block.prev_phys_block` accordingly
                next_next_phys_block.as_mut().prev_phys_block = Some(next_phys_block.cast());
            } else {
                // Can fit exactly.
                debug_assert_eq!(grow_by, next_phys_block_size);

                // Update `next_next_phys_block.prev_phys_block` accordingly
                next_next_phys_block.as_mut().prev_phys_block = Some(block.cast());
            }

            block.as_mut().common.size = new_size | SIZE_USED;
            self.allocated += new_size - old_size;

            return Some(ptr);
        }

        // In-place moving reallocation
        // ------------------------------------------------------------------

        // The non-moving reallocation was failure. Now try the moving approach.
        // I.e., grow into the previous free block as well.
        // Get the previous block. If there isn't such a block, the moving
        // approach will not improve the situation anyway, so return `None`.
        let prev_phys_block = block.as_ref().common.prev_phys_block?;
        let prev_phys_block_size_and_flags = prev_phys_block.as_ref().size;

        // Fail it isn't a free block.
        if (prev_phys_block_size_and_flags & SIZE_USED) != 0 {
            return None;
        }

        let prev_phys_block_size = prev_phys_block_size_and_flags;
        debug_assert_eq!(
            prev_phys_block_size,
            prev_phys_block_size_and_flags & SIZE_SIZE_MASK
        );

        // Now we know it's really a free block.
        moving_clearance += prev_phys_block_size;

        // Decide the starting address of the payload
        let unaligned_ptr =
            prev_phys_block.as_ptr() as *mut u8 as usize + mem::size_of::<UsedBlockHdr>();
        let new_ptr = NonNull::new_unchecked(
            ((unaligned_ptr + new_layout.align() - 1) & !(new_layout.align() - 1)) as *mut u8,
        );

        // Calculate the new block size
        let new_overhead = new_ptr.as_ptr() as usize - prev_phys_block.as_ptr() as usize;
        let new_size = new_overhead.checked_add(new_layout.size())?;
        let new_size = new_size.checked_add(GRANULARITY - 1)? & !(GRANULARITY - 1);
        if new_size > moving_clearance {
            // Can't fit
            return None;
        }

        // Unlink the existing free blocks included in `moving_clearance`
        self.unlink_free_block(prev_phys_block.cast(), prev_phys_block_size);
        let next_phys_block_size_and_flags = next_phys_block.as_ref().size;
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            let next_phys_block_size = next_phys_block_size_and_flags;
            debug_assert_eq!(
                next_phys_block_size,
                next_phys_block_size_and_flags & SIZE_SIZE_MASK
            );
            self.unlink_free_block(next_phys_block.cast(), next_phys_block_size);
        }

        // Move the existing data into the new memory block.
        core::ptr::copy(
            ptr.as_ptr(),
            new_ptr.as_ptr(),
            new_layout.size().min(old_size - overhead),
        );

        // We'll replace `prev_phys_block` with a new used block.
        let mut new_block = prev_phys_block.cast::<UsedBlockHdr>();

        if new_size == moving_clearance {
            // The allocation completely fills this free block.
            // Update `prev_phys_block` accordingly
            moving_clearance_end.as_mut().prev_phys_block = Some(new_block.cast());
        } else {
            // The allocation partially fills this free block. Create a new
            // free block header at `new_block + new_size..new_block
            // + moving_clearance`.
            let mut new_free_block: NonNull<FreeBlockHdr> =
                NonNull::new_unchecked(new_block.cast::<u8>().as_ptr().add(new_size)).cast();
            let mut new_free_block_size = moving_clearance - new_size;

            // If the following block (`moving_clearance_end`) is a free block...
            let moving_clearance_end_size_and_flags = moving_clearance_end.as_ref().size;
            if (moving_clearance_end_size_and_flags & SIZE_USED) == 0 {
                let moving_clearance_end_size = moving_clearance_end_size_and_flags;
                debug_assert_eq!(
                    moving_clearance_end_size,
                    moving_clearance_end_size_and_flags & SIZE_SIZE_MASK
                );

                // Then we should merge this existing free block (`moving_clearance_end`)
                // into the new one (`new_free_block`).
                self.unlink_free_block(moving_clearance_end.cast(), moving_clearance_end_size);
                new_free_block_size += moving_clearance_end_size_and_flags;

                let mut next_next_phys_block = moving_clearance_end.as_ref().next_phys_block();
                next_next_phys_block.as_mut().prev_phys_block = Some(new_free_block.cast());
            } else {
                // We can't merge a used block (`moving_clearance_end`) and
                // a free block (`new_free_block`).
                moving_clearance_end.as_mut().prev_phys_block = Some(new_free_block.cast());
            }

            new_free_block.as_mut().common =
                BlockHdr::new(new_free_block_size, Some(new_block.cast()));
            self.link_free_block(new_free_block, new_free_block_size);
        }

        // Turn `new_block` into a used memory block and initialize the used block
        // header. `prev_phys_block` is already set.
        new_block.as_mut().common.size = new_size | SIZE_USED;

        // Place a header pointer (used by `used_block_hdr_for_allocation`)
        if new_layout.align() >= GRANULARITY {
            (*UsedBlockPad::get_for_allocation(new_ptr)).block_hdr = new_block;
        }
        self.allocated += new_size - old_size;

        Some(new_ptr)
    }

    /// Returns the size of the maximum used of the heap
    pub fn maximum(&self) -> usize {
        self.maximum
    }

    /// Returns the size of the used part of the heap
    pub fn allocated(&self) -> usize {
        self.allocated
    }

    /// Returns the size of the used part of the heap
    pub fn total(&self) -> usize {
        self.total
    }

    /// Returns the size of the free part of the heap
    pub fn free(&self) -> usize {
        self.total - self.allocated
    }

    /// Enumerate memory blocks in the specified memory pool.
    ///
    /// # Safety
    ///
    /// `pool` must precisely represent a memory pool that belongs to `self`.
    /// Specifically, its starting address must be the one that was previously
    /// passed to [`Self::insert_free_block_ptr`], and its length must be the
    /// sum of the return values of that call to `insert_free_block_ptr` and
    /// all subsequent calls to [`Self::append_free_block_ptr`] that have been
    /// made to expand this memory pool.
    ///
    /// # Examples
    ///
    /// ```
    /// use rlsf::Tlsf;
    /// use std::{mem::MaybeUninit, alloc::Layout, ptr::{NonNull, slice_from_raw_parts_mut}};
    ///
    /// static mut POOL: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
    /// let pool_ptr = NonNull::new(unsafe { POOL.as_mut_ptr() }).unwrap();
    ///
    /// let mut tlsf: Tlsf<'_, u16, u16, 12, 16> = Tlsf::new();
    ///
    /// // Insert a memory pool. We need to remember the actual pool size
    /// // to safely use `Tlsf::iter_blocks` later.
    /// let pool_len = unsafe { tlsf.insert_free_block_ptr(pool_ptr) }.unwrap().get();
    /// let pool_ptr = NonNull::new(
    ///     slice_from_raw_parts_mut(pool_ptr.as_ptr() as *mut u8, pool_len)
    /// ).unwrap();
    ///
    /// // A closure to calculate the remaining free space
    /// let free_bytes = |p: &Tlsf<'_, _, _, 12, 16>| unsafe { p.iter_blocks(pool_ptr) }
    ///     .filter(|block_info| !block_info.is_occupied())
    ///     .map(|block_info| block_info.max_payload_size())
    ///     .sum::<usize>();
    ///
    /// // Allocate memory
    /// let free_bytes1 = dbg!(free_bytes(&tlsf));
    /// tlsf.allocate(Layout::new::<u64>()).unwrap();
    /// let free_bytes2 = dbg!(free_bytes(&tlsf));
    ///
    /// // Since we have allocated memory, we should have less free space now
    /// assert!(free_bytes2 < free_bytes1);
    /// ```
    pub unsafe fn iter_blocks(
        &self,
        pool: NonNull<[u8]>,
    ) -> impl Iterator<Item = BlockInfo<'_>> + Send + '_ {
        let len = nonnull_slice_len(pool);

        // Round up the starting address in the same way as
        // `insert_free_block_ptr` does.
        //
        // In `insert_free_block_ptr` there's a minimum pool size cut-off, and
        // when that happens, `insert_free_block_ptr` returns `None`. In such a
        // case, as per this method's safety requirements, "the sum of the
        // return values of ..." is undefined, so the user is not supposed to
        // even call this method. This means this method don't have to repeat
        // this cut-off step from `insert_free_block_ptr`.
        let unaligned_start = pool.as_ptr() as *mut u8 as usize;
        let mut start = unaligned_start.wrapping_add(GRANULARITY - 1) & !(GRANULARITY - 1);
        let mut len = len.saturating_sub(start.wrapping_sub(unaligned_start));

        core::iter::from_fn(move || {
            if len == 0 {
                None
            } else {
                let block_hdr = &*(start as *const BlockHdr);
                let block_size = block_hdr.size & SIZE_SIZE_MASK;

                // Advance the cursor
                len -= block_size;
                start = start.wrapping_add(block_size);

                Some(BlockInfo { block_hdr })
            }
        })
        .filter(|block_info| {
            // Exclude sentinel blocks
            (block_info.block_hdr.size & SIZE_SENTINEL) == 0
        })
    }
}

/// Allows the caller of [`Tlsf::iter_blocks`] to examine the properties of a
/// memory block in a [`Tlsf`] memory pool.
#[derive(Clone, Copy)]
pub struct BlockInfo<'a> {
    block_hdr: &'a BlockHdr,
}

impl core::fmt::Debug for BlockInfo<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BlockInfo")
            .field("ptr", &self.as_ptr_range())
            .field("size", &self.size())
            .field("is_occupied", &self.is_occupied())
            .finish()
    }
}

impl BlockInfo<'_> {
    /// Get this block's size, including the header.
    #[inline]
    pub fn size(&self) -> usize {
        self.block_hdr.size & SIZE_SIZE_MASK
    }

    /// Get the block's size minus the header.
    ///
    /// This represents the maximum size of an allocation with an alignment
    /// smaller than [`GRANULARITY`] that can fit in this block.
    #[inline]
    pub fn max_payload_size(&self) -> usize {
        self.size() - GRANULARITY / 2
    }

    /// Get this block's address range as a raw slice pointer.
    #[inline]
    pub fn as_ptr(&self) -> NonNull<[u8]> {
        nonnull_slice_from_raw_parts(NonNull::from(self.block_hdr).cast(), self.size())
    }

    /// Get this block's address range as two raw pointers.
    #[inline]
    fn as_ptr_range(&self) -> core::ops::Range<*mut u8> {
        let start = self.block_hdr as *const _ as *mut u8;
        let end = start.wrapping_add(self.size());
        start..end
    }

    /// Get a flag indicating wthether this block is in use.
    #[inline]
    pub fn is_occupied(&self) -> bool {
        (self.block_hdr.size & SIZE_USED) != 0
    }
}
