// Minimal SpinLock wrapper for kernel allocator crate.
// This provides a SpinLock compatible with the kernel's interface
// but using the spin crate under the hood.

use core::ops::{Deref, DerefMut};

/// A spin lock wrapper.
pub struct SpinLock<T: ?Sized> {
    inner: spin::Mutex<T>,
}

impl<T> SpinLock<T> {
    #[inline]
    pub const fn new(val: T) -> Self {
        Self {
            inner: spin::Mutex::new(val),
        }
    }

    /// Lock without disabling interrupts.
    /// In the full kernel this also disables interrupts; here it's just a lock.
    #[inline]
    pub fn irqsave_lock(&self) -> SpinLockGuard<'_, T> {
        SpinLockGuard {
            inner: self.inner.lock(),
        }
    }

    /// Lock (same as irqsave_lock since we don't have interrupt control).
    #[inline]
    pub fn lock(&self) -> SpinLockGuard<'_, T> {
        SpinLockGuard {
            inner: self.inner.lock(),
        }
    }
}

pub struct SpinLockGuard<'a, T: ?Sized + 'a> {
    inner: spin::MutexGuard<'a, T>,
}

impl<'a, T: ?Sized> Deref for SpinLockGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.inner.deref()
    }
}

impl<'a, T: ?Sized> DerefMut for SpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.inner.deref_mut()
    }
}