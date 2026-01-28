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

// Implement a lock based on UnsafeCell to optimize performance on single core.
// The APIs of this lock should be compatible with that in tinyrwlock.

use crate::intrusive::Adapter;
use core::{
    cell::UnsafeCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

#[derive(Debug)]
pub struct NoLock<T: ?Sized> {
    data: UnsafeCell<T>,
}

impl<T: Default> Default for NoLock<T> {
    fn default() -> Self {
        Self::new(Default::default())
    }
}

#[derive(Debug)]
pub struct NoLockWriteGuard<'a, T: 'a + ?Sized> {
    inner: *mut T,
    _a: PhantomData<&'a mut T>,
}

impl<T: ?Sized> Deref for NoLockWriteGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.inner }
    }
}

impl<T: ?Sized> DerefMut for NoLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.inner }
    }
}

#[derive(Debug)]
pub struct NoLockReadGuard<'a, T: 'a + ?Sized> {
    inner: *const T,
    _a: PhantomData<&'a mut T>,
}

impl<T: ?Sized> Deref for NoLockReadGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.inner }
    }
}

impl<T> NoLock<T> {
    pub const fn new(val: T) -> Self {
        Self {
            data: UnsafeCell::new(val),
        }
    }
}

impl<T: ?Sized> NoLock<T> {
    pub fn try_write(&self) -> Option<NoLockWriteGuard<'_, T>> {
        Some(NoLockWriteGuard {
            inner: self.data.get(),
            _a: PhantomData,
        })
    }

    pub fn try_read(&self) -> Option<NoLockReadGuard<'_, T>> {
        Some(NoLockReadGuard {
            inner: self.data.get() as *const _,
            _a: PhantomData,
        })
    }

    pub fn write(&self) -> NoLockWriteGuard<'_, T> {
        self.try_write().unwrap()
    }

    pub fn read(&self) -> NoLockReadGuard<'_, T> {
        self.try_read().unwrap()
    }

    pub fn reader_count(&self) -> usize {
        usize::MAX
    }

    pub fn writer_count(&self) -> usize {
        usize::MAX
    }
}

unsafe impl<T: ?Sized + Send> Send for NoLock<T> {}
unsafe impl<T: ?Sized + Send + Sync> Sync for NoLock<T> {}
unsafe impl<T: ?Sized + Send + Sync> Send for NoLockWriteGuard<'_, T> {}
unsafe impl<T: ?Sized + Send + Sync> Sync for NoLockWriteGuard<'_, T> {}
unsafe impl<T: ?Sized + Sync> Send for NoLockReadGuard<'_, T> {}
unsafe impl<T: ?Sized + Sync> Sync for NoLockReadGuard<'_, T> {}

#[derive(Default, Debug)]
pub struct INoLock<T: Sized, A: Adapter<T>> {
    lock: NoLock<()>,
    _a: PhantomData<(T, A)>,
}

impl<T: Sized, A: Adapter<T>> INoLock<T, A> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            lock: NoLock::new(()),
            _a: PhantomData,
        }
    }

    #[inline]
    fn this(&self) -> &T {
        let ptr = self as *const _ as *const u8;
        let base = unsafe { ptr.sub(A::offset()) as *const T };
        unsafe { &*base }
    }

    #[inline]
    fn this_mut(&self) -> &mut T {
        let ptr = self as *const _ as *mut u8;
        let base = unsafe { ptr.sub(A::offset()) as *mut T };
        unsafe { &mut *base }
    }

    #[inline]
    pub fn read(&self) -> NoLockReadGuard<T> {
        let inner = self.this() as *const T;
        NoLockReadGuard {
            inner,
            _a: PhantomData,
        }
    }

    #[inline]
    pub fn try_read(&self) -> Option<NoLockReadGuard<'_, T>> {
        let inner = self.this() as *const T;
        Some(NoLockReadGuard {
            inner,
            _a: PhantomData,
        })
    }

    #[inline]
    pub fn write(&self) -> NoLockWriteGuard<'_, T> {
        let inner = self.this_mut() as *mut T;
        NoLockWriteGuard {
            inner,
            _a: PhantomData,
        }
    }

    #[inline]
    pub fn try_write(&self) -> Option<NoLockWriteGuard<'_, T>> {
        let inner = self.this_mut() as *mut T;
        Some(NoLockWriteGuard {
            inner,
            _a: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read() {
        let l = NoLock::new(42);
        let r = l.read();
        assert_eq!(*r, 42);
    }

    #[test]
    fn test_write() {
        let l = NoLock::new(0);
        let mut w = l.write();
        *w = 42;
        drop(w);
        let r = l.read();
        assert_eq!(*r, 42);
    }
}
