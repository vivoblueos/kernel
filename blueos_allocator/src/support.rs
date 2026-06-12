// Support utilities for blueos_allocator.
// These are ported from kernel/src/support.rs for use in this standalone crate.

use core::{mem::MaybeUninit, ptr::NonNull};

#[inline]
pub const fn align_down_size(addr: usize, align: usize) -> usize {
    addr & !(align - 1)
}

#[inline]
pub const fn align_up_size(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

#[inline]
pub fn align_up(addr: *mut u8, align: usize) -> *mut u8 {
    align_up_size(addr as usize, align) as *mut u8
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/71941>
#[inline]
pub fn nonnull_slice_from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> NonNull<[T]> {
    unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len)) }
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/71146>
#[inline]
pub fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    unsafe { (*(ptr.as_ptr() as *const [MaybeUninit<T>])).len() }
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/74265>
#[inline]
pub fn nonnull_slice_start<T>(ptr: NonNull<[T]>) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(ptr.as_ptr() as *mut T) }
}