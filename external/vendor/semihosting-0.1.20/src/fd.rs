// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Owned and borrowed Unix-like file descriptors.
//!
//! This is identical to [`std::os::fd`](https://doc.rust-lang.org/std/os/fd/index.html),
//! but available with no-std.
//!
//! Note that this crate does not provide `{As,Into,From}RawFd` traits. They have been effectively
//! obsoleted by io-safety, and now using `AsFd`, `From<... > for OwnedFd`, or `Into<OwnedFd>`
//! is recommended. To convert to `RawFd`, you need first convert it to `BorrowedFd` or
//! `OwnedFd` the above way and then call `BorrowedFd::as_raw_fd` or `OwnedFd::{as,into}_raw_fd`.
//! This redundancy is intentional, as it serves as a reminder that it is usually not
//! recommended.

#![allow(clippy::undocumented_unsafe_blocks)] // TODO

use core::{ffi, fmt, marker::PhantomData, mem::ManuallyDrop};

use crate::sys;

/// Raw file descriptors.
pub type RawFd = ffi::c_int;

// 16-bit targets has 16-bit c_int.
#[cfg(not(target_pointer_width = "16"))]
static_assert!(core::mem::size_of::<RawFd>() == core::mem::size_of::<u32>());
#[cfg(target_pointer_width = "16")]
static_assert!(core::mem::size_of::<RawFd>() == core::mem::size_of::<u16>());

/// A borrowed file descriptor.
///
/// This has a lifetime parameter to tie it to the lifetime of something that
/// owns the file descriptor.
///
/// This uses `repr(transparent)` and has the representation of a host file
/// descriptor, so it can be used in FFI in places where a file descriptor is
/// passed as an argument, it is not captured or consumed, and it never has the
/// value `-1`.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct BorrowedFd<'fd> {
    fd: RawFd,
    _phantom: PhantomData<&'fd OwnedFd>,
}

/// An owned file descriptor.
///
/// This closes the file descriptor on drop.
///
/// This uses `repr(transparent)` and has the representation of a host file
/// descriptor, so it can be used in FFI in places where a file descriptor is
/// passed as a consumed argument or returned as an owned value, and it never
/// has the value `-1`.
#[repr(transparent)]
pub struct OwnedFd {
    fd: RawFd,
}

impl BorrowedFd<'_> {
    /// Return a `BorrowedFd` holding the given raw file descriptor.
    ///
    /// # Safety
    ///
    /// The resource pointed to by `fd` must remain open for the duration of
    /// the returned `BorrowedFd`, and it must not have the value `-1`.
    #[inline]
    pub const unsafe fn borrow_raw(fd: RawFd) -> Self {
        assert!(fd != -1);
        Self { fd, _phantom: PhantomData }
    }

    /// Extracts the raw file descriptor.
    #[allow(clippy::trivially_copy_pass_by_ref)] // align to AsRawFd::as_raw_fd
    #[inline]
    pub const fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl OwnedFd {
    /// Constructs a new instance of `Self` from the given raw file descriptor.
    ///
    /// # Safety
    ///
    /// The resource pointed to by `fd` must be open and suitable for assuming
    /// ownership. The resource must not require any cleanup other than `close`.
    #[inline]
    pub const unsafe fn from_raw_fd(fd: RawFd) -> Self {
        assert!(fd != -1);
        Self { fd }
    }

    /// Extracts the raw file descriptor.
    #[inline]
    pub const fn as_raw_fd(&self) -> RawFd {
        self.fd
    }

    /// Consumes this object, returning the raw underlying file descriptor.
    #[inline]
    #[must_use = "losing the raw file descriptor may leak resources"]
    pub fn into_raw_fd(self) -> RawFd {
        let this = ManuallyDrop::new(self);
        this.fd
    }
}

impl Drop for OwnedFd {
    #[inline]
    fn drop(&mut self) {
        if sys::should_close(self) {
            // Note that errors are ignored when closing a file descriptor. The
            // reason for this is that if an error occurs we don't actually know if
            // the file descriptor was closed or not, and if we retried (for
            // something like EINTR), we might close another valid file descriptor
            // opened after we closed ours.
            let _ = unsafe { sys::close(self.as_raw_fd()) };
        }
    }
}

impl fmt::Debug for BorrowedFd<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BorrowedFd").field("fd", &self.fd).finish()
    }
}
impl fmt::Debug for OwnedFd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OwnedFd").field("fd", &self.fd).finish()
    }
}

/// A trait to borrow the file descriptor from an underlying object.
pub trait AsFd {
    /// Borrows the file descriptor.
    fn as_fd(&self) -> BorrowedFd<'_>;
}

impl<T: ?Sized + AsFd> AsFd for &T {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        T::as_fd(self)
    }
}
impl<T: ?Sized + AsFd> AsFd for &mut T {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        T::as_fd(self)
    }
}

impl AsFd for BorrowedFd<'_> {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        *self
    }
}
impl AsFd for OwnedFd {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        // SAFETY: `OwnedFd` and `BorrowedFd` have the same validity
        // invariants, and the `BorrowedFd` is bounded by the lifetime
        // of `&self`.
        unsafe { BorrowedFd::borrow_raw(self.fd) }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<T: ?Sized + AsFd> AsFd for alloc::boxed::Box<T> {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        (**self).as_fd()
    }
}
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<T: ?Sized + AsFd> AsFd for alloc::rc::Rc<T> {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        (**self).as_fd()
    }
}
#[cfg(target_has_atomic = "ptr")]
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<T: ?Sized + AsFd> AsFd for alloc::sync::Arc<T> {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        (**self).as_fd()
    }
}

#[cfg(any(feature = "stdio", feature = "fs"))]
macro_rules! impl_as_fd {
    ($($ty:ty),* $(,)?) => {$(
        impl crate::fd::AsFd for $ty {
            #[inline]
            fn as_fd(&self) -> crate::fd::BorrowedFd<'_> {
                self.0.as_fd()
            }
        }
    )*};
}
#[cfg(feature = "fs")]
macro_rules! impl_from_fd {
    ($($ty:ty),* $(,)?) => {$(
        impl From<$ty> for OwnedFd {
            #[inline]
            fn from(this: $ty) -> Self {
                this.0
            }
        }
        impl From<OwnedFd> for $ty {
            #[inline]
            fn from(owned_fd: OwnedFd) -> Self {
                Self(owned_fd)
            }
        }
    )*};
}
