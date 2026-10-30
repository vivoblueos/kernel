use core::{cell::UnsafeCell, mem::MaybeUninit, ptr::NonNull};

/// Polyfill for <https://github.com/rust-lang/rust/issues/71941>
#[inline]
pub fn nonnull_slice_from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> NonNull<[T]> {
    unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len)) }
}

/// Polyfill for  <https://github.com/rust-lang/rust/issues/71146>
///
/// # Safety
///
/// `ptr` must be dereferencable. This is a limitation of the polyfill.
#[inline]
pub unsafe fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    // FIXME: Use `NonNull<[T]>::len` (stabilized in Rust 1.63)
    // Safety: We are just reading the slice length embedded in the fat
    //         pointer and not dereferencing the pointer. We also convert it
    //         to `*mut [MaybeUninit<UnsafeCell<u8>>]` just in case because the
    //         slice might be uninitialized and there might be outstanding
    //         mutable references to the slice.
    (&*(ptr.as_ptr() as *const [MaybeUninit<UnsafeCell<T>>])).len()
}

// Polyfill for <https://github.com/rust-lang/rust/issues/74265>
#[inline]
pub fn nonnull_slice_start<T>(ptr: NonNull<[T]>) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(ptr.as_ptr() as *mut T) }
}

/// Get the one-past-end pointer of a slice pointer.
///
/// # Safety
///
/// `ptr` must be dereferencable. This is a limitation of [`nonnull_slice_len`].
#[inline]
pub unsafe fn nonnull_slice_end<T>(ptr: NonNull<[T]>) -> *mut T {
    (ptr.as_ptr() as *mut T).wrapping_add(nonnull_slice_len(ptr))
}

/// Get a pointer to a field in `NonNull<Struct>`.
macro_rules! nn_field {
    ($ptr:expr, $($tt:tt)*) => {
        core::ptr::addr_of_mut!((*$ptr.as_ptr()).$($tt)*)
    };
}

/// Round `ptr`'s address down to the previous `align` bytes boundary.
#[inline]
#[rustversion::since(1.84)]
pub unsafe fn round_down(ptr: *mut u8, align: usize) -> *mut u8 {
    debug_assert!(align.is_power_of_two());
    ptr.map_addr(|addr| addr & !(align - 1))
}

/// Round `ptr`'s address down to the previous `align` bytes boundary.
#[inline]
#[rustversion::before(1.84)]
pub unsafe fn round_down(ptr: *mut u8, align: usize) -> *mut u8 {
    debug_assert!(align.is_power_of_two());
    (ptr as usize & !(align - 1)) as *mut u8
}

/// Round `ptr`'s address up to the next `align` bytes boundary.
#[inline]
#[rustversion::since(1.84)]
pub unsafe fn round_up(ptr: *mut u8, align: usize) -> *mut u8 {
    debug_assert!(align.is_power_of_two());
    ptr.map_addr(|addr| addr.wrapping_add(align - 1) & !(align - 1))
}

/// Round `ptr`'s address up to the next `align` bytes boundary.
#[inline]
#[rustversion::before(1.84)]
pub unsafe fn round_up(ptr: *mut u8, align: usize) -> *mut u8 {
    debug_assert!(align.is_power_of_two());
    ((ptr as usize).wrapping_add(align - 1) & !(align - 1)) as *mut u8
}
