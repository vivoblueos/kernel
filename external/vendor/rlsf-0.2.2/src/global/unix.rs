use const_default1::ConstDefault;
use core::{
    marker::PhantomData,
    ptr::{addr_of_mut, null_mut, NonNull},
};

use super::GlobalTlsfOptions;

const MIN_ALIGN: usize = crate::GRANULARITY;

/// The allocation unit, which is intentionally set to be larger than the usual
/// page sizes to reduce overhead. TODO: Make this adjustable
///
/// A smaller value is used on Miri because it somehow speeds up execution.
const ALLOC_UNIT: usize = if cfg!(miri) { 1 << 14 } else { 1 << 16 };

pub struct Mutex(());

impl ConstDefault for Mutex {
    const DEFAULT: Self = Self(());
}

/// `pthread_mutex_t` might be unsafe to move, so we can't put it in `Mutex`.
static mut MUTEX: libc::pthread_mutex_t = libc::PTHREAD_MUTEX_INITIALIZER;

impl Mutex {
    #[inline]
    pub fn lock(&self) {
        unsafe { libc::pthread_mutex_lock(addr_of_mut!(MUTEX)) };
    }

    #[inline]
    pub fn unlock(&self) {
        unsafe { libc::pthread_mutex_unlock(addr_of_mut!(MUTEX)) };
    }
}

pub struct Source<Options>(PhantomData<fn() -> Options>);

impl<Options> ConstDefault for Source<Options> {
    const DEFAULT: Self = Self(PhantomData);
}

/// The memory page size minus 1. Set by `Mutex::lock`.
static mut PAGE_SIZE_M1: usize = 0;
#[cold]
fn init_page_size() -> usize {
    unsafe {
        let page_size = (libc::sysconf(libc::_SC_PAGESIZE) as usize).max(ALLOC_UNIT);
        if !page_size.is_power_of_two() {
            libc::abort();
        }
        PAGE_SIZE_M1 = page_size - 1;

        // Such a small memory page size is quite unusual.
        if page_size < MIN_ALIGN {
            libc::abort();
        }

        PAGE_SIZE_M1
    }
}

#[inline]
fn ensure_page_size_m1() -> usize {
    let page_size_m1 = unsafe { PAGE_SIZE_M1 };
    if page_size_m1 == 0 {
        // `init_page_size` returns the initialized value for
        // code size optimization
        init_page_size()
    } else {
        page_size_m1
    }
}

unsafe impl<Options: GlobalTlsfOptions> crate::flex::FlexSource for Source<Options> {
    #[inline]
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        let page_size_m1 = ensure_page_size_m1();
        let num_bytes = min_size.checked_add(page_size_m1)? & !page_size_m1;

        let ptr = libc::mmap(
            null_mut(),
            num_bytes,
            libc::PROT_WRITE | libc::PROT_READ,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
            -1,
            0,
        );

        if ptr == libc::MAP_FAILED {
            return None;
        }

        NonNull::new(core::ptr::slice_from_raw_parts_mut(
            ptr as *mut u8,
            num_bytes,
        ))
    }

    #[inline]
    // `MAP_FIXED_NOREPLACE` is only supported by Linux 4.17 and later.
    #[cfg(target_os = "linux")]
    unsafe fn realloc_inplace_grow(
        &mut self,
        ptr: NonNull<[u8]>,
        min_new_len: usize,
    ) -> Option<usize> {
        use crate::utils::nonnull_slice_len;

        if !Options::COALESCE_POOLS {
            return None;
        }

        let page_size_m1 = ensure_page_size_m1();
        let num_bytes = min_new_len.checked_add(page_size_m1)? & !page_size_m1;
        let num_growth_bytes = num_bytes - nonnull_slice_len(ptr);

        let ptr_end = (ptr.as_ptr() as *mut u8).wrapping_add(nonnull_slice_len(ptr));

        let ptr_growth_start = libc::mmap(
            ptr_end as _,
            num_growth_bytes,
            libc::PROT_WRITE | libc::PROT_READ,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_FIXED_NOREPLACE,
            -1,
            0,
        );

        if ptr_growth_start != ptr_end as _ {
            // We are on an old Linux kernel, and `MAP_FIXED_NOREPLACE` was
            // not respected.
            libc::munmap(ptr_growth_start, num_growth_bytes);
            None
        } else if ptr_growth_start == libc::MAP_FAILED {
            None
        } else {
            Some(num_bytes)
        }
    }

    #[inline]
    #[cfg(target_os = "linux")]
    fn supports_realloc_inplace_grow(&self) -> bool {
        Options::COALESCE_POOLS
    }

    // Not implementing `dealloc` because there is no safe way to destruct
    // a registered global allocator anyway.

    #[inline]
    fn min_align(&self) -> usize {
        // Return a conservative yet enough-for-optimization constant number
        MIN_ALIGN
    }
}
