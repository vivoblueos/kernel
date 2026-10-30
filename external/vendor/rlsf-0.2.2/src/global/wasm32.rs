use const_default1::ConstDefault;
use core::{arch::wasm32, marker::PhantomData, ptr::NonNull};

use super::GlobalTlsfOptions;

pub struct Mutex(());

impl ConstDefault for Mutex {
    const DEFAULT: Self = Self(());
}

#[cfg(not(target_feature = "atomics"))]
impl Mutex {
    // Single-threaded WebAssembly environment
    #[inline]
    pub fn lock(&self) {}

    #[inline]
    pub fn unlock(&self) {}
}

pub struct Source<Options>(PhantomData<fn() -> Options>);

impl<Options> ConstDefault for Source<Options> {
    const DEFAULT: Self = Self(PhantomData);
}

const MEM: u32 = 0;
const PAGE_SIZE_LOG2: u32 = 16;
const PAGE_SIZE: usize = 1 << PAGE_SIZE_LOG2;

unsafe impl<Options: GlobalTlsfOptions> crate::flex::FlexSource for Source<Options> {
    #[inline]
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        let num_pages = min_size.checked_add(PAGE_SIZE - 1)? / PAGE_SIZE;
        let num_bytes = num_pages * PAGE_SIZE;

        let old_num_pages = wasm32::memory_grow(MEM, num_pages);

        if old_num_pages == usize::MAX {
            // failure
            None
        } else {
            Some(
                NonNull::new(core::ptr::slice_from_raw_parts_mut(
                    (old_num_pages * PAGE_SIZE) as *mut u8,
                    num_bytes,
                ))
                // Assume the old memory size is non-zero. It's likely to be
                // true because otherwise there wouldn't be even a stack space.
                .unwrap_or_else(|| wasm32::unreachable()),
            )
        }
    }

    #[inline]
    unsafe fn realloc_inplace_grow(
        &mut self,
        ptr: NonNull<[u8]>,
        min_new_len: usize,
    ) -> Option<usize> {
        if !Options::COALESCE_POOLS {
            return None;
        }

        let ptr_page = ptr.as_ptr() as *mut u8 as usize / PAGE_SIZE;
        if ptr_page != wasm32::memory_size(MEM) {
            // We can't grow the memory from `ptr`; someone else has grown it
            // past `ptr`, and we don't own that part
            return None;
        }

        let new_num_pages = min_new_len.checked_add(PAGE_SIZE - 1)? / PAGE_SIZE;
        let new_len = new_num_pages * PAGE_SIZE;

        if wasm32::memory_grow(MEM, new_num_pages - ptr_page) == usize::MAX {
            // failure
            None
        } else {
            Some(new_len)
        }
    }

    #[inline]
    fn supports_realloc_inplace_grow(&self) -> bool {
        Options::COALESCE_POOLS
    }

    // Turns out, `is_contiguous_growable` can't return `true` because
    // other code may issue `memory.grow` without `unsafe` blocks.

    #[inline]
    fn min_align(&self) -> usize {
        PAGE_SIZE
    }
}
