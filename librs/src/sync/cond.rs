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

use blueos_infra::no_let_underscore::IgnoreResult;
use core::{
    ffi::c_int,
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::{clockid_t, timespec};

use super::mutex::Mutex;

type Result<T, E = c_int> = core::result::Result<T, E>;

/// The attributes of a condition variable.
///
/// The default clock is `CLOCK_REALTIME`, which is clock id 1 in the C
/// library's numbering - not 0, which is what a zeroed struct would hold.
#[derive(Copy, Clone)]
#[repr(C)]
pub struct CondAttr {
    pub clock: clockid_t,
    pub pshared: c_int,
}

impl Default for CondAttr {
    fn default() -> Self {
        Self {
            clock: crate::time::deadline::C_CLOCK_REALTIME,
            pshared: crate::pthread::PTHREAD_PROCESS_PRIVATE,
        }
    }
}

#[repr(align(8))]
pub struct Cond {
    cur: AtomicUsize,
    prev: AtomicUsize,
    /// The clock `pthread_cond_timedwait()` measures its deadline against.
    ///
    /// POSIX Issue 8: "The clock to measure abstime against shall instead
    /// come from the condition variable's clock attribute which can be set by
    /// pthread_condattr_setclock() prior to the condition variable's
    /// creation. If no clock attribute has been set, the default shall be
    /// CLOCK_REALTIME."
    ///
    /// The value is a **C library** clock id (newlib numbering), the same
    /// numbering the caller uses everywhere else.
    clock: clockid_t,
}

impl Cond {
    pub fn new() -> Self {
        Self {
            cur: AtomicUsize::new(0),
            prev: AtomicUsize::new(0),
            clock: crate::time::deadline::C_CLOCK_REALTIME,
        }
    }

    /// Builds a condition variable that measures its deadlines on `clock`.
    pub fn with_clock(clock: clockid_t) -> Self {
        Self {
            cur: AtomicUsize::new(0),
            prev: AtomicUsize::new(0),
            clock,
        }
    }

    /// The clock this condition variable measures its deadlines against.
    pub fn clock(&self) -> clockid_t {
        self.clock
    }

    fn wake(&self, count: usize) -> Result<(), c_int> {
        // This is formally correct as long as we don't have more than u32::MAX threads.
        let prev = self.prev.load(Ordering::Relaxed);
        self.cur.store(prev.wrapping_add(1), Ordering::Relaxed);

        crate::sync::futex_wake(&self.cur, count);
        Ok(())
    }

    pub fn broadcast(&self) -> Result<(), c_int> {
        self.wake(usize::MAX)
    }

    pub fn signal(&self) -> Result<(), c_int> {
        self.broadcast()
    }

    /// Waits on the condition variable until `deadline` passes.
    ///
    /// `deadline` is an **absolute** time on a specific clock, as POSIX
    /// requires of `pthread_cond_timedwait` and `pthread_cond_clockwait`.
    ///
    /// Returns `Err(ETIMEDOUT)` when the deadline passed before the
    /// condition variable was signalled. The mutex is owned again on return
    /// in either case - POSIX requires that even on timeout.
    pub fn timedwait(
        &self,
        mutex: &Mutex,
        deadline: &crate::time::deadline::Deadline,
    ) -> Result<()> {
        self.wait_inner(mutex, Some(deadline))
    }

    fn wait_inner(
        &self,
        mutex: &Mutex,
        timeout: Option<&crate::time::deadline::Deadline>,
    ) -> Result<()> {
        self.wait_inner_generic(
            || mutex.unlock(),
            || mutex.lock(),
            timeout,
        )
    }

    pub fn wait_inner_typedmutex<'lock, T>(
        &self,
        guard: crate::sync::MutexGuard<'lock, T>,
    ) -> crate::sync::MutexGuard<'lock, T> {
        let mut newguard = None;
        let lock = guard.mutex;
        self.wait_inner_generic(
            move || {
                drop(guard);
                Ok(())
            },
            || {
                newguard = Some(lock.lock());
                Ok(())
            },
            None,
        )
        .unwrap();
        newguard.unwrap()
    }

    // TODO: FUTEX_REQUEUE
    fn wait_inner_generic(
        &self,
        unlock: impl FnOnce() -> Result<()>,
        lock: impl FnOnce() -> Result<()>,
        deadline: Option<&crate::time::deadline::Deadline>,
    ) -> Result<()> {
        // TODO: Error checking for certain types (i.e. robust and errorcheck) of mutexes, e.g. if the
        // mutex is not locked.
        let current = self.cur.load(Ordering::Relaxed);
        self.prev.store(current, Ordering::Relaxed);

        unlock().ignore_result();

        match deadline {
            Some(deadline) => {
                // The futex reports the deadline expiring as `Ok(false)`. That
                // is not an error in itself - POSIX wants ETIMEDOUT reported
                // to the caller, and it wants the mutex owned again either
                // way.
                let timed_out = match crate::sync::futex_wait_until(&self.cur, current, deadline) {
                    // Woken up: the condition variable was signalled.
                    Ok(true) => false,
                    // The deadline passed while we were waiting.
                    Ok(false) => true,
                    // A hard error (EAGAIN for a stale value) still means we
                    // have to re-acquire the mutex; the wait itself did not
                    // time out.
                    Err(_) => false,
                };

                // The mutex has to be owned again on return, even on timeout
                // - POSIX says so explicitly. The re-acquisition therefore
                // must not be bounded by the deadline: it has already
                // expired, and a timed re-acquisition would report
                // ETIMEDOUT and leave the caller without the mutex.
                lock().ignore_result();

                if timed_out {
                    return Err(libc::ETIMEDOUT);
                }
            }
            None => {
                crate::sync::futex_wait(&self.cur, current, None);
                lock().ignore_result();
            }
        }
        Ok(())
    }
    pub fn wait(&self, mutex: &Mutex) -> Result<()> {
        self.wait_inner(mutex, None)
    }
}
