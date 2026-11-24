// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! Non-atomic read/write borrow checking with externally synchronized state.
//!
//! This module does not mask interrupts or prevent scheduling. Its caller must
//! serialize borrow-state access, including guard destruction. The kernel's UP
//! `SpinLock` wrapper supplies this protection; other users must supply their own.

use crate::marker::NotThreadSafe;
use core::{
    cell::{Cell, UnsafeCell},
    ops::{Deref, DerefMut},
};

/// A non-atomic read/write lock whose borrow bookkeeping needs external protection.
///
/// The lock is not `Sync`; it does not provide cross-thread or interrupt exclusion
/// by itself. Obtaining guards requires an unsafe call that establishes the
/// protection needed by both acquisition and subsequent guard destruction.
pub struct LocalRwLock<T: ?Sized> {
    state: BorrowState,
    data: UnsafeCell<T>,
}

// Zero is idle, WRITER is exclusive, and all other values count readers.
struct BorrowState(Cell<usize>);

impl<T> LocalRwLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            state: BorrowState::new(),
            data: UnsafeCell::new(data),
        }
    }
}

impl<T: ?Sized> LocalRwLock<T> {
    /// Attempts to acquire an exclusive payload borrow.
    ///
    /// # Safety
    /// The caller must serialize every access to this lock's borrow state,
    /// including acquisitions, count queries, and destruction of any returned
    /// guard. No concurrent or reentrant state access may interrupt one of these
    /// operations. Protection must also be established when the guard is dropped;
    /// protecting only this call is insufficient.
    #[inline(always)]
    pub unsafe fn try_write(&self) -> Option<WriteGuard<'_, T>> {
        self.state.try_write().then(|| WriteGuard {
            state: &self.state,
            data: self.data.get(),
            _not_send: NotThreadSafe,
        })
    }

    /// Attempts to acquire a shared payload borrow.
    ///
    /// # Safety
    /// The caller must uphold the state-access and guard-destruction protection
    /// requirements of [`Self::try_write`].
    #[inline(always)]
    pub unsafe fn try_read(&self) -> Option<ReadGuard<'_, T>> {
        self.state.try_read().then(|| ReadGuard {
            state: &self.state,
            data: self.data.get(),
            _not_send: NotThreadSafe,
        })
    }

    /// Returns the number of active read guards.
    ///
    /// # Safety
    /// This query must be serialized with every other access to the borrow state,
    /// including guard destruction, as described in [`Self::try_write`].
    #[inline(always)]
    pub unsafe fn reader_count(&self) -> usize {
        self.state.reader_count()
    }

    /// Returns one if a write guard is active, otherwise zero.
    ///
    /// # Safety
    /// This query must be serialized with every other access to the borrow state,
    /// including guard destruction, as described in [`Self::try_write`].
    #[inline(always)]
    pub unsafe fn writer_count(&self) -> usize {
        self.state.writer_count()
    }
}

impl LocalRwLock<()> {
    /// Acquires a write borrow for an externally supplied payload.
    ///
    /// This is a transitional adapter for existing intrusive callers. Borrow-state
    /// exclusion alone does not establish the validity of an owner projection.
    ///
    /// # Safety
    /// The caller must uphold the protection requirements of [`Self::try_write`].
    /// In addition, `data` must be aligned, non-null, point to an initialized `T`,
    /// and remain valid for the returned guard's lifetime. It must permit the
    /// shared and exclusive references exposed by the guard, with no conflicting
    /// accesses through other pointers or references. The payload must not overlap
    /// the borrow bookkeeping accessed through this lock.
    #[inline(always)]
    pub unsafe fn project_write<T>(&self, data: *mut T) -> Option<WriteGuard<'_, T>> {
        self.state.try_write().then(|| WriteGuard {
            state: &self.state,
            data,
            _not_send: NotThreadSafe,
        })
    }
}

impl BorrowState {
    const WRITER: usize = usize::MAX;

    const fn new() -> Self {
        Self(Cell::new(0))
    }

    #[inline(always)]
    fn try_read(&self) -> bool {
        let n = self.0.get();
        if n >= Self::WRITER - 1 {
            return false;
        }
        self.0.set(n + 1);
        true
    }

    #[inline(always)]
    fn try_write(&self) -> bool {
        if self.0.get() != 0 {
            return false;
        }
        self.0.set(Self::WRITER);
        true
    }

    #[inline(always)]
    fn release_read(&self) {
        let n = self.0.get();
        assert!(n != 0 && n != Self::WRITER);
        self.0.set(n - 1);
    }

    #[inline(always)]
    fn release_write(&self) {
        assert_eq!(self.0.get(), Self::WRITER);
        self.0.set(0);
    }

    #[inline(always)]
    fn reader_count(&self) -> usize {
        match self.0.get() {
            Self::WRITER => 0,
            n => n,
        }
    }

    #[inline(always)]
    fn writer_count(&self) -> usize {
        usize::from(self.0.get() == Self::WRITER)
    }
}

/// An exclusive payload borrow. Dropping it updates externally protected state.
#[must_use]
pub struct WriteGuard<'a, T: ?Sized> {
    state: &'a BorrowState,
    data: *mut T,
    _not_send: NotThreadSafe,
}

/// A shared payload borrow. Dropping it updates externally protected state.
#[must_use]
pub struct ReadGuard<'a, T: ?Sized> {
    state: &'a BorrowState,
    data: *const T,
    _not_send: NotThreadSafe,
}

impl<T: ?Sized> Deref for WriteGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<T: ?Sized> DerefMut for WriteGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }
}

impl<T: ?Sized> Deref for ReadGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<T: ?Sized> Drop for WriteGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.state.release_write();
    }
}

impl<T: ?Sized> Drop for ReadGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        self.state.release_read();
    }
}

impl<T: ?Sized> core::fmt::Debug for LocalRwLock<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("LocalRwLock { .. }")
    }
}

impl<T: ?Sized> core::fmt::Debug for WriteGuard<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("LocalWriteGuard { .. }")
    }
}

impl<T: ?Sized> core::fmt::Debug for ReadGuard<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("LocalReadGuard { .. }")
    }
}

#[cfg(test)]
mod tests {
    use super::{BorrowState, Cell};

    #[test]
    fn exclusion_and_release() {
        let s = BorrowState::new();
        assert!(s.try_write());
        assert!(!s.try_write());
        assert!(!s.try_read());
        s.release_write();
        assert!(s.try_read());
        assert!(s.try_read());
        assert!(!s.try_write());
        s.release_read();
        assert!(!s.try_write());
        s.release_read();
        assert!(s.try_write());
        s.release_write();
        assert_eq!(s.reader_count(), 0);
        assert_eq!(s.writer_count(), 0);
    }

    #[test]
    fn reader_overflow_cannot_unlock() {
        let s = BorrowState(Cell::new(BorrowState::WRITER - 2));
        assert!(s.try_read());
        assert!(!s.try_read());
        assert!(!s.try_write());
        assert_eq!(s.reader_count(), BorrowState::WRITER - 1);
        s.release_read();
        assert!(s.try_read());
    }
}
