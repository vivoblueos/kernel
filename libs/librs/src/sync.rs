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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

#[allow(unused_imports)]
use blueos_header::syscalls::NR::{AtomicWait, AtomicWake};
use blueos_scal::bk_syscall;
use core::{
    cell::UnsafeCell,
    ffi::c_int,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::timespec;

pub mod barrier;
pub mod cond;
pub mod mutex;
pub mod once;
pub mod rwlock;
pub mod semaphore;
pub mod waitval;

type Result<T, E = c_int> = core::result::Result<T, E>;

pub(crate) fn futex_wake(atomic: &AtomicUsize, val: usize) -> c_int {
    let mut woken: usize = val;
    bk_syscall!(
        AtomicWake,
        atomic.as_ptr() as usize,
        &mut woken as *mut usize
    );
    woken as c_int
}

pub(crate) fn futex_wait(atomic: &AtomicUsize, val: usize, timeout: Option<&timespec>) -> c_int {
    bk_syscall!(
        AtomicWait,
        atomic.as_ptr() as usize,
        val,
        timeout.map_or(core::ptr::null(), |t| t as *const timespec)
    ) as c_int
}

#[repr(i32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FutexWaitResult {
    Waited, // possibly spurious
    Stale,  // outdated value
    TimedOut,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AttemptStatus {
    Desired,
    Waiting,
    Other,
}

/// Convenient wrapper around the "futex" system call for
/// synchronization implementations.
#[repr(C)]
pub(crate) struct AtomicLock {
    pub(crate) atomic: AtomicUsize,
}

impl Deref for AtomicLock {
    type Target = AtomicUsize;

    fn deref(&self) -> &Self::Target {
        &self.atomic
    }
}

impl AtomicLock {
    pub const fn new(value: usize) -> Self {
        Self {
            atomic: AtomicUsize::new(value),
        }
    }
    pub fn notify_one(&self) {
        futex_wake(&self.atomic, 1);
    }
    pub fn notify_all(&self) {
        futex_wake(&self.atomic, usize::MAX);
    }
    pub fn wait_if(&self, value: usize, timeout_opt: Option<&timespec>) {
        self.wait_if_raw(value, timeout_opt);
    }
    pub fn wait_if_raw(&self, value: usize, timeout_opt: Option<&timespec>) -> c_int {
        futex_wait(&self.atomic, value, timeout_opt)
    }

    /// A general way to efficiently wait for what might be a long time, using two closures:
    ///
    /// - `attempt` = Attempt to modify the atomic value to any
    ///   desired state.
    /// - `mark_long` = Attempt to modify the atomic value to sign
    ///   that it want's to get notified when waiting is done.
    ///
    /// Both of these closures are allowed to spuriously give a
    /// non-success return value, they are used only as optimization
    /// hints. However, what counts as a "desired value" may differ
    /// per closure. Therefore, `mark_long` can notify a value as
    /// "desired" in order to get `attempt` retried immediately.
    ///
    /// The `long` parameter is the only one which actually cares
    /// about the specific value of your atomics. This is needed
    /// because it needs to pass this to the futex system call in
    /// order to avoid race conditions where the atomic could be
    /// modified to the desired value before the call is complete and
    /// we receive the wakeup notification.
    pub fn wait_until<F1, F2>(&self, attempt: F1, mark_long: F2, long: usize)
    where
        F1: Fn(&AtomicUsize) -> AttemptStatus,
        F2: Fn(&AtomicUsize) -> AttemptStatus,
    {
        wait_until_generic(&self.atomic, attempt, mark_long, long)
    }
}

pub fn wait_until_generic<F1, F2>(word: &AtomicUsize, attempt: F1, mark_long: F2, long: usize)
where
    F1: Fn(&AtomicUsize) -> AttemptStatus,
    F2: Fn(&AtomicUsize) -> AttemptStatus,
{
    // First, try spinning for really short durations
    for _ in 0..999 {
        core::hint::spin_loop();
        if attempt(word) == AttemptStatus::Desired {
            return;
        }
    }

    // One last attempt, to initiate "previous"
    let mut previous = attempt(word);

    // Ok, that seems to take quite some time. Let's go into a
    // longer, more patient, wait.
    loop {
        if previous == AttemptStatus::Desired {
            return;
        }

        if
        // If we or somebody else already initiated a long
        // wait, OR
        previous == AttemptStatus::Waiting ||
            // Otherwise, unless our attempt to initiate a long
            // wait informed us that we might be done waiting
            mark_long(word) != AttemptStatus::Desired
        {
            futex_wait(word, long, None);
        }

        previous = attempt(word);
    }
}

pub(crate) const UNLOCKED: usize = 0;
pub(crate) const LOCKED: usize = 1;
pub(crate) const WAITING: usize = 2;

pub struct GenericMutex<T> {
    pub(crate) lock: AtomicLock,
    content: UnsafeCell<T>,
}

pub(crate) unsafe fn manual_try_lock_generic(word: &AtomicUsize) -> bool {
    word.compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
        .is_ok()
}
pub(crate) unsafe fn manual_lock_generic(word: &AtomicUsize) {
    crate::sync::wait_until_generic(
        word,
        |lock| {
            lock.compare_exchange_weak(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
                .map(|_| AttemptStatus::Desired)
                .unwrap_or_else(|e| match e {
                    WAITING => AttemptStatus::Waiting,
                    _ => AttemptStatus::Other,
                })
        },
        |lock| match lock
            // TODO: Ordering
            .compare_exchange_weak(LOCKED, WAITING, Ordering::SeqCst, Ordering::SeqCst)
            .unwrap_or_else(|e| e)
        {
            UNLOCKED => AttemptStatus::Desired,
            WAITING => AttemptStatus::Waiting,
            _ => AttemptStatus::Other,
        },
        WAITING,
    );
}
pub(crate) unsafe fn manual_unlock_generic(word: &AtomicUsize) {
    if word.swap(UNLOCKED, Ordering::Release) == WAITING {
        crate::sync::futex_wake(word, usize::MAX);
    }
}

impl<T> GenericMutex<T> {
    /// Create a new mutex
    pub const fn new(content: T) -> Self {
        Self {
            lock: AtomicLock::new(UNLOCKED),
            content: UnsafeCell::new(content),
        }
    }
    /// Create a new mutex that is already locked. This is a more
    /// efficient way to do the following:
    /// ```rust
    /// let mut mutex = Mutex::new(());
    /// mutex.manual_lock();
    /// ```
    pub unsafe fn locked(content: T) -> Self {
        Self {
            lock: AtomicLock::new(LOCKED),
            content: UnsafeCell::new(content),
        }
    }

    /// Tries to lock the mutex, fails if it's already locked. Manual means
    /// it's up to you to unlock it after mutex. Returns the last atomic value
    /// on failure. You should probably not worry about this, it's used for
    /// internal optimizations.
    pub unsafe fn manual_try_lock(&self) -> Result<&mut T, c_int> {
        if unsafe { manual_try_lock_generic(&self.lock) } {
            Ok(unsafe { &mut *self.content.get() })
        } else {
            Err(0)
        }
    }
    /// Lock the mutex, returning the inner content. After doing this, it's
    /// your responsibility to unlock it after usage. Mostly useful for FFI:
    /// Prefer normal .lock() where possible.
    pub unsafe fn manual_lock(&self) -> &mut T {
        unsafe { manual_lock_generic(&self.lock) };
        unsafe { &mut *self.content.get() }
    }
    /// Unlock the mutex, if it's locked.
    pub unsafe fn manual_unlock(&self) {
        unsafe { manual_unlock_generic(&self.lock) }
    }
    pub fn as_ptr(&self) -> *mut T {
        self.content.get()
    }

    /// Tries to lock the mutex and returns a guard that automatically unlocks
    /// the mutex when it falls out of scope.
    pub fn try_lock(&self) -> Option<MutexGuard<T>> {
        unsafe {
            self.manual_try_lock().ok().map(|content| MutexGuard {
                mutex: self,
                content,
            })
        }
    }
    /// Locks the mutex and returns a guard that automatically unlocks the
    /// mutex when it falls out of scope.
    pub fn lock(&self) -> MutexGuard<T> {
        MutexGuard {
            mutex: self,
            content: unsafe { self.manual_lock() },
        }
    }
}

pub struct MutexGuard<'a, T: 'a> {
    pub(crate) mutex: &'a GenericMutex<T>,
    content: &'a mut T,
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.content
    }
}

impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.content
    }
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        unsafe {
            self.mutex.manual_unlock();
        }
    }
}
