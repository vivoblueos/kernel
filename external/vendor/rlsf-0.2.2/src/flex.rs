//! An allocator with flexible backing stores
use const_default1::ConstDefault;
use core::{alloc::Layout, debug_assert, ptr::NonNull, unimplemented};

use crate::utils::round_down;

use super::{
    int::BinInteger,
    utils::{
        nonnull_slice_end, nonnull_slice_from_raw_parts, nonnull_slice_len, nonnull_slice_start,
    },
    Tlsf, GRANULARITY,
};

/// The trait for dynamic storage allocators that can back [`FlexTlsf`].
pub unsafe trait FlexSource {
    /// Allocate a memory block of the requested minimum size.
    ///
    /// Returns the address range of the allocated memory block.
    ///
    /// # Safety
    ///
    /// `min_size` must be a multiple of [`GRANULARITY`]. `min_size` must not
    /// be zero.
    #[inline]
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        let _ = min_size;
        None
    }

    /// Attempt to grow the specified allocation without moving it. Returns
    /// the final allocation size (which must be greater than or equal to
    /// `min_new_len`) on success.
    ///
    /// # Safety
    ///
    /// `ptr` must be an existing allocation made by this
    /// allocator. `min_new_len` must be greater than or equal to `ptr.len()`.
    #[inline]
    unsafe fn realloc_inplace_grow(
        &mut self,
        ptr: NonNull<[u8]>,
        min_new_len: usize,
    ) -> Option<usize> {
        let _ = (ptr, min_new_len);
        None
    }

    /// Deallocate a previously allocated memory block.
    ///
    /// # Safety
    ///
    /// `ptr` must denote an existing allocation made by this allocator.
    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<[u8]>) {
        let _ = ptr;
        unimplemented!("`supports_dealloc` returned `true`, but `dealloc` is not implemented");
    }

    /// Check if this allocator implements [`Self::dealloc`].
    ///
    /// If this method returns `false`, [`FlexTlsf`] will not call `dealloc` to
    /// release memory blocks. It also applies some optimizations.
    ///
    /// The returned value must be constant for a particular instance of `Self`.
    #[inline]
    fn supports_dealloc(&self) -> bool {
        false
    }

    /// Check if this allocator implements [`Self::realloc_inplace_grow`].
    ///
    /// If this method returns `false`, [`FlexTlsf`] will not call
    /// `realloc_inplace_grow` to attempt to grow memory blocks. It also applies
    /// some optimizations.
    ///
    /// The returned value must be constant for a particular instance of `Self`.
    #[inline]
    fn supports_realloc_inplace_grow(&self) -> bool {
        false
    }

    /// Returns `true` if this allocator is implemented by managing one
    /// contiguous region, which is grown every time `alloc` or
    /// `realloc_inplace_grow` is called.
    ///
    /// For example, in WebAssembly, there is usually only one continuous
    /// memory region available for data processing, and the only way to acquire
    /// more memory is to grow this region by executing `memory.grow`
    /// instructions. An implementation of `FlexSource` based on this system
    /// would use this instruction to implement both `alloc` and
    /// `realloc_inplace_grow` methods. Therefore, it's pointless for
    /// [`FlexTlsf`] to call `alloc` when `realloc_inplace_grow` fails. This
    /// method can be used to remove such redundant calls to `alloc`.
    ///
    /// The returned value must be constant for a particular instance of `Self`.
    #[inline]
    fn is_contiguous_growable(&self) -> bool {
        false
    }

    /// Get the minimum alignment of allocations made by this allocator.
    /// [`FlexTlsf`] may be less efficient if this method returns a value
    /// less than [`GRANULARITY`].
    ///
    /// The returned value must be constant for a particular instance of `Self`.
    #[inline]
    fn min_align(&self) -> usize {
        1
    }
}

trait FlexSourceExt: FlexSource {
    #[inline]
    fn use_growable_pool(&self) -> bool {
        // `growable_pool` is used for deallocation and pool growth.
        // Let's not think about the wasted space caused when this method
        // returns `false`.
        self.supports_dealloc() || self.supports_realloc_inplace_grow() || FORCE_POOL_FTR
    }
}

impl<T: FlexSource> FlexSourceExt for T {}

/// Wraps [`core::alloc::GlobalAlloc`] to implement the [`FlexSource`] trait.
///
/// Since this type does not implement [`FlexSource::realloc_inplace_grow`],
/// it is likely to end up with terribly fragmented memory pools.
#[derive(Default, Debug, Copy, Clone)]
pub struct GlobalAllocAsFlexSource<T, const ALIGN: usize>(pub T);

impl<T: core::alloc::GlobalAlloc, const ALIGN: usize> GlobalAllocAsFlexSource<T, ALIGN> {
    const ALIGN: usize = if ALIGN.is_power_of_two() {
        if ALIGN < GRANULARITY {
            GRANULARITY
        } else {
            ALIGN
        }
    } else {
        panic!("`ALIGN` is not power of two")
    };
}

impl<T: ConstDefault, const ALIGN: usize> ConstDefault for GlobalAllocAsFlexSource<T, ALIGN> {
    const DEFAULT: Self = Self(ConstDefault::DEFAULT);
}

unsafe impl<T: core::alloc::GlobalAlloc, const ALIGN: usize> FlexSource
    for GlobalAllocAsFlexSource<T, ALIGN>
{
    #[inline]
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        let layout = Layout::from_size_align(min_size, Self::ALIGN)
            .ok()?
            .pad_to_align();
        // Safety: The caller upholds that `min_size` is not zero
        let start = self.0.alloc(layout);
        let start = NonNull::new(start)?;
        Some(nonnull_slice_from_raw_parts(start, layout.size()))
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<[u8]>) {
        // Safety: This layout was previously used for allocation, during which
        //         the layout was checked for validity
        let layout = Layout::from_size_align_unchecked(nonnull_slice_len(ptr), Self::ALIGN);

        // Safety: `start` denotes an existing allocation with layout `layout`
        self.0.dealloc(ptr.as_ptr() as _, layout);
    }

    fn supports_dealloc(&self) -> bool {
        true
    }

    #[inline]
    fn min_align(&self) -> usize {
        Self::ALIGN
    }
}

/// A wrapper of [`Tlsf`] that automatically acquires fresh memory pools from
/// [`FlexSource`].
#[derive(Debug)]
pub struct FlexTlsf<Source: FlexSource, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize>
{
    /// The lastly created memory pool.
    growable_pool: Option<Pool>,
    source: Source,
    tlsf: Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>,
}

#[derive(Debug, Copy, Clone)]
struct Pool {
    /// The starting address of the memory allocation.
    alloc_start: NonNull<u8>,
    /// The length of the memory allocation.
    alloc_len: usize,
    /// The length of the memory pool created within the allocation.
    /// This might be slightly less than `alloc_len`.
    pool_len: usize,
}

// Safety: `Pool` is totally thread-safe
unsafe impl Send for Pool {}
unsafe impl Sync for Pool {}

/// If set, unconditionally creates [`PoolFtr`] and sets
/// [`FlexTlsf::growable_pool`] regardless of a provided [`FlexSource`]'s
/// capabilities.
// [tag:flex_force_pool_ftr_miri]
const FORCE_POOL_FTR: bool = cfg!(miri);

/// Pool footer stored at the end of each pool. It's only used when
/// supports_dealloc() == true` or [`FORCE_POOL_FTR`] is set.
///
/// The footer is stored in the sentinel block's unused space or any padding
/// present at the end of each pool. This is why `PoolFtr` can't be larger than
/// two `usize`s.
#[repr(C)]
#[derive(Copy, Clone)]
struct PoolFtr {
    /// The previous allocation. Forms a singly-linked list.
    prev_alloc: Option<NonNull<[u8]>>,
}

const _: () = if core::mem::size_of::<PoolFtr>() != GRANULARITY / 2 {
    panic!("bad `PoolFtr` size");
};

impl PoolFtr {
    /// Get a pointer to `PoolFtr` for a given allocation.
    ///
    /// # Safety
    ///
    /// `ptr` must be dereferencable. This is a limitation of
    /// [`nonnull_slice_end`].
    #[inline]
    unsafe fn get_for_alloc(alloc: NonNull<[u8]>, alloc_align: usize) -> *mut Self {
        let alloc_end = nonnull_slice_end(alloc);
        let mut ptr = alloc_end.wrapping_sub(core::mem::size_of::<Self>());
        // If `alloc_end` is not well-aligned, we need to adjust the location
        // of `PoolFtr`
        if alloc_align < core::mem::align_of::<Self>() {
            ptr = round_down(ptr, core::mem::align_of::<Self>());
        }
        ptr as _
    }
}

/// Initialization with a [`FlexSource`] provided by [`Default::default`]
impl<
        Source: FlexSource + Default,
        FLBitmap: BinInteger,
        SLBitmap: BinInteger,
        const FLLEN: usize,
        const SLLEN: usize,
    > Default for FlexTlsf<Source, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    #[inline]
    fn default() -> Self {
        Self::new(Source::default())
    }
}

/// Initialization with a [`FlexSource`] provided by [`ConstDefault::DEFAULT`]
impl<
        Source: FlexSource + ConstDefault,
        FLBitmap: BinInteger,
        SLBitmap: BinInteger,
        const FLLEN: usize,
        const SLLEN: usize,
    > ConstDefault for FlexTlsf<Source, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    /// An empty pool.
    const DEFAULT: Self = Self::new(Source::DEFAULT);
}

impl<
        Source: FlexSource,
        FLBitmap: BinInteger,
        SLBitmap: BinInteger,
        const FLLEN: usize,
        const SLLEN: usize,
    > FlexTlsf<Source, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    /// Construct a new `FlexTlsf` object.
    #[inline]
    pub const fn new(source: Source) -> Self {
        Self {
            source,
            tlsf: Tlsf::new(),
            growable_pool: None,
        }
    }

    /// Borrow the contained `Source`.
    #[inline]
    pub fn source_ref(&self) -> &Source {
        &self.source
    }

    /// Mutably borrow the contained `Source`.
    ///
    /// # Safety
    ///
    /// The caller must not replace the `Source` with another one or modify
    /// any existing allocations in the `Source`.
    #[inline]
    pub unsafe fn source_mut_unchecked(&mut self) -> &mut Source {
        &mut self.source
    }

    /// Attempt to allocate a block of memory.
    ///
    /// Returns the starting address of the allocated memory block on success;
    /// `None` otherwise.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time (assuming `Source`'s methods
    /// do so as well).
    #[cfg_attr(target_arch = "wasm32", inline(never))]
    pub fn allocate(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        if let Some(x) = self.tlsf.allocate(layout) {
            return Some(x);
        }

        self.increase_pool_to_contain_allocation(layout)?;

        self.tlsf.allocate(layout).or_else(|| {
            // Not a hard error, but it's still unexpected because
            // `increase_pool_to_contain_allocation` was supposed to make this
            // allocation possible
            debug_assert!(
                false,
                "the allocation failed despite the effort by \
                `increase_pool_to_contain_allocation`"
            );
            None
        })
    }

    /// Increase the amount of memory pool to guarantee the success of the
    /// given allocation. Returns `Some(())` on success.
    #[inline]
    fn increase_pool_to_contain_allocation(&mut self, layout: Layout) -> Option<()> {
        let use_growable_pool = self.source.use_growable_pool();

        // How many extra bytes we need to get from the source for the
        // allocation to success?
        let extra_bytes_well_aligned =
            Tlsf::<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>::pool_size_to_contain_allocation(
                layout,
            )?;

        // The sentinel block + the block to store the allocation
        debug_assert!(extra_bytes_well_aligned >= GRANULARITY * 2);

        if let Some(growable_pool) = self.growable_pool.filter(|_| use_growable_pool) {
            // Try to extend an existing memory pool first.
            let new_pool_len_desired = growable_pool
                .pool_len
                .checked_add(extra_bytes_well_aligned)?;

            // The following assertion should not trip because...
            //  - `extra_bytes_well_aligned` returns a value that is at least
            //    as large as `GRANULARITY * 2`.
            //  - `growable_pool.alloc_len - growable_pool.pool_len` must be
            //    less than `GRANULARITY * 2` because of
            //    `insert_free_block_ptr`'s implementation.
            debug_assert!(new_pool_len_desired >= growable_pool.alloc_len);

            // Safety: `new_pool_end_desired >= growable_pool.alloc_len`, and
            //         `(growable_pool.alloc_start, growable_pool.alloc_len)`
            //         represents a previous allocation.
            if let Some(new_alloc_len) = unsafe {
                self.source.realloc_inplace_grow(
                    nonnull_slice_from_raw_parts(
                        growable_pool.alloc_start,
                        growable_pool.alloc_len,
                    ),
                    new_pool_len_desired,
                )
            } {
                if self.source.supports_dealloc() || FORCE_POOL_FTR {
                    // Move `PoolFtr`. Note that `PoolFtr::alloc_start` is
                    // still uninitialized because this allocation is still in
                    // `self.growable_pool`, so we only have to move
                    // `PoolFtr::prev_alloc_end`.

                    // Safety: The memory range represented by `growable_pool`
                    // is dereferencable
                    let old_pool_ftr = unsafe {
                        PoolFtr::get_for_alloc(
                            nonnull_slice_from_raw_parts(
                                growable_pool.alloc_start,
                                growable_pool.alloc_len,
                            ),
                            self.source.min_align(),
                        )
                    };

                    // Safety: The memory range represented by `growable_pool`
                    // extended to `new_alloc_len` is dereferencable
                    let new_pool_ftr = unsafe {
                        PoolFtr::get_for_alloc(
                            nonnull_slice_from_raw_parts(growable_pool.alloc_start, new_alloc_len),
                            self.source.min_align(),
                        )
                    };

                    // Safety: Both `*new_pool_ftr` and `*old_pool_ftr`
                    //         represent pool footers we control
                    unsafe { *new_pool_ftr = *old_pool_ftr };
                }

                let num_appended_len = unsafe {
                    // Safety: `self.source` allocated some memory after
                    //         `alloc_start + pool_len`, so it shouldn't be
                    //         null
                    let append_start = NonNull::new_unchecked(
                        growable_pool
                            .alloc_start
                            .as_ptr()
                            .wrapping_add(growable_pool.pool_len),
                    );
                    // Safety: `append_start` follows an existing memory pool,
                    //         and the contained bytes are owned by us
                    self.tlsf
                        .append_free_block_ptr(nonnull_slice_from_raw_parts(
                            append_start,
                            new_alloc_len - growable_pool.pool_len,
                        ))
                };

                // This assumption is based on `extra_bytes_well_aligned`'s
                // implementation. The `debug_assert!` above depends on this.
                debug_assert!(
                    (growable_pool.pool_len + num_appended_len) - new_alloc_len < GRANULARITY * 2
                );

                self.growable_pool = Some(Pool {
                    alloc_start: growable_pool.alloc_start,
                    alloc_len: new_alloc_len,
                    pool_len: growable_pool.pool_len + num_appended_len,
                });

                return Some(());
            } // if let Some(new_alloc_len) = ... realloc_inplace_grow

            if self.source.is_contiguous_growable() {
                // `is_contiguous_growable`
                // indicates that `alloc` will also be fruitless because
                // `realloc_inplace_grow` failed.
                return None;
            }
        } // if let Some(growable_pool) = self.growable_pool

        // Create a brand new allocation. `source.min_align` indicates the
        // minimum alignment that the created allocation will satisfy.
        // `extra_bytes_well_aligned` is the pool size that can contain the
        // allocation *if* the pool was well-aligned. If `source.min_align` is
        // not well-aligned enough, we need to allocate extra bytes.
        let extra_bytes = if self.source.min_align() < GRANULARITY {
            //
            //                    wasted                             wasted
            //                     ╭┴╮                               ╭──┴──╮
            //                     ┌─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┐
            //         Allocation: │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │ │
            //                     └─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┘
            //                       ┌───────┬───────┬───────┬───────┐
            // Pool created on it:   │       │       │       │       │
            //                       └───────┴───────┴───────┴───────┘
            //                       ╰───┬───╯
            //                      GRANULARITY
            //
            extra_bytes_well_aligned.checked_add(GRANULARITY)?
        } else {
            extra_bytes_well_aligned
        };

        // Safety: `extra_bytes` is non-zero and aligned to `GRANULARITY` bytes
        let alloc = unsafe { self.source.alloc(extra_bytes)? };

        let is_well_aligned = self.source.min_align() >= super::GRANULARITY;

        // Safety: The passed memory block is what we acquired from
        //         `self.source`, so we have the ownership
        let pool_len = unsafe {
            if is_well_aligned {
                self.tlsf.insert_free_block_ptr_aligned(alloc)
            } else {
                self.tlsf.insert_free_block_ptr(alloc)
            }
        }
        .unwrap_or_else(|| unsafe {
            debug_assert!(false, "`pool_size_to_contain_allocation` is an impostor");
            // Safety: It's unreachable
            core::hint::unreachable_unchecked()
        })
        .get();

        if self.source.supports_dealloc() || FORCE_POOL_FTR {
            // Link the new memory pool's `PoolFtr::prev_alloc_end` to the
            // previous pool (`self.growable_pool`).
            // Safety: `alloc` is dereferencable
            let pool_ftr = unsafe { PoolFtr::get_for_alloc(alloc, self.source.min_align()) };
            let prev_alloc = self
                .growable_pool
                .map(|p| nonnull_slice_from_raw_parts(p.alloc_start, p.alloc_len));
            // Safety: `(*pool_ftr).prev_alloc` is within a pool footer
            //         we control
            unsafe { (*pool_ftr).prev_alloc = prev_alloc };
        }

        if use_growable_pool {
            self.growable_pool = Some(Pool {
                alloc_start: nonnull_slice_start(alloc),
                // Safety: `alloc` is derefencable
                alloc_len: unsafe { nonnull_slice_len(alloc) },
                pool_len,
            });
        }

        Some(())
    }

    /// Deallocate a previously allocated memory block.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time (assuming `Source`'s methods
    /// do so as well).
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///  - The memory block must have been allocated with the same alignment
    ///    ([`Layout::align`]) as `align`.
    ///
    #[cfg_attr(target_arch = "wasm32", inline(never))]
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, align: usize) {
        // Safety: Upheld by the caller
        self.tlsf.deallocate(ptr, align)
    }

    /// Deallocate a previously allocated memory block with an unknown alignment.
    ///
    /// Unlike `deallocate`, this function does not require knowing the
    /// allocation's alignment but might be less efficient.
    ///
    /// # Time Complexity
    ///
    /// This method will complete in constant time (assuming `Source`'s methods
    /// do so as well).
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///
    pub(crate) unsafe fn deallocate_unknown_align(&mut self, ptr: NonNull<u8>) {
        // Safety: Upheld by the caller
        self.tlsf.deallocate_unknown_align(ptr)
    }

    /// Get the actual usable size of a previously allocated memory block.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via some
    ///    instance of `Self`.
    ///  - The call must happen-before the deallocation or reallocation of the
    ///    memory block.
    ///
    #[cfg(feature = "unstable")]
    #[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "unstable")))]
    pub unsafe fn allocation_usable_size(ptr: NonNull<u8>) -> usize {
        Tlsf::<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>::size_of_allocation_unknown_align(ptr)
    }

    /// Shrink or grow a previously allocated memory block.
    ///
    /// Returns the new starting address of the memory block on success;
    /// `None` otherwise.
    ///
    /// # Time Complexity
    ///
    /// Unlike other methods, this method will complete in linear time
    /// (`O(old_size)`), assuming `Source`'s methods do so as well.
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
        new_layout: Layout,
    ) -> Option<NonNull<u8>> {
        // Do this early so that the compiler can de-duplicate the evaluation of
        // `size_of_allocation`, which is done here as well as in
        // `Tlsf::reallocate`.
        let old_size = Tlsf::<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>::size_of_allocation(
            ptr,
            new_layout.align(),
        );

        // Safety: Upheld by the caller
        if let Some(x) = self.tlsf.reallocate(ptr, new_layout) {
            return Some(x);
        }

        // Allocate a whole new memory block. The following code section looks
        // the same as the one in `Tlsf::reallocate`, but `self.allocation`
        // here refers to `FlexTlsf::allocate`, which inserts new meory pools
        // as necessary.
        let new_ptr = self.allocate(new_layout)?;

        // Move the existing data into the new location
        debug_assert!(new_layout.size() >= old_size);
        core::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), old_size);

        // Deallocate the old memory block.
        self.deallocate(ptr, new_layout.align());

        Some(new_ptr)
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
    pub(crate) unsafe fn size_of_allocation_unknown_align(ptr: NonNull<u8>) -> usize {
        // Safety: Upheld by the caller
        Tlsf::<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>::size_of_allocation_unknown_align(ptr)
    }

    /// Take a provenance-less allocation pointer and restore its provenance
    /// so that it can be passed to [`Self::dealllocate`].
    ///
    /// [`Self::growable_pool`] must be in use for this method to work
    /// correctly.
    ///
    /// This method panics if no memory pools contain the provided pointer.
    #[cfg(miri)]
    pub(crate) fn restore_provenance(&self, ptr: *mut u8) -> *mut u8 {
        let pool = iter_pools(&self.growable_pool, self.source.min_align())
            .filter(|pool| pool.as_ptr() as *mut u8 <= ptr)
            .max()
            .expect("original pool not found");

        pool.as_ptr().cast::<u8>().with_addr(ptr.addr())
    }
}

/// Iterate over all memory pools linked to [`FlexTlsf::growable_pool`].
#[inline]
fn iter_pools(growable_pool: &Option<Pool>, align: usize) -> impl Iterator<Item = NonNull<[u8]>> {
    let cur_alloc_or_none =
        growable_pool.map(|p| nonnull_slice_from_raw_parts(p.alloc_start, p.alloc_len));

    core::iter::successors(cur_alloc_or_none, move |&cur_alloc| {
        // Safety: We control the referenced pool footer
        let cur_ftr = unsafe { *PoolFtr::get_for_alloc(cur_alloc, align) };

        cur_ftr.prev_alloc
    })
}

impl<Source: FlexSource, FLBitmap, SLBitmap, const FLLEN: usize, const SLLEN: usize> Drop
    for FlexTlsf<Source, FLBitmap, SLBitmap, FLLEN, SLLEN>
{
    fn drop(&mut self) {
        if self.source.supports_dealloc() {
            debug_assert!(self.source.use_growable_pool());

            // Deallocate all memory pools
            for cur_alloc in iter_pools(&self.growable_pool, self.source.min_align()) {
                // Safety: It's an allocation we allocated from `self.source`
                unsafe { self.source.dealloc(cur_alloc) };
            }
        }
    }
}

#[cfg(test)]
mod tests;
