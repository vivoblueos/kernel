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

use core::{
    ffi::c_int,
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::{clockid_t, timespec};

use super::mutex::Mutex;

type Result<T, E = c_int> = core::result::Result<T, E>;

#[derive(Default, Copy, Clone)]
pub struct CondAttr {
    pub clock: clockid_t,
    pub pshared: c_int,
}

#[repr(align(8))]
pub struct Cond {
    cur: AtomicUsize,
    prev: AtomicUsize,
}

impl Cond {
    pub fn new() -> Self {
        Self {
            cur: AtomicUsize::new(0),
            prev: AtomicUsize::new(0),
        }
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

    pub fn timedwait(&self, mutex: &Mutex, timeout: &timespec) -> Result<()> {
        self.wait_inner(mutex, Some(timeout))
    }

    fn wait_inner(&self, mutex: &Mutex, timeout: Option<&timespec>) -> Result<()> {
        self.wait_inner_generic(
            || mutex.unlock(),
            || mutex.lock(),
            |timeout| mutex.lock_with_timeout(timeout),
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
            |_| unreachable!(),
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
        lock_with_timeout: impl FnOnce(&timespec) -> Result<()>,
        deadline: Option<&timespec>,
    ) -> Result<()> {
        // TODO: Error checking for certain types (i.e. robust and errorcheck) of mutexes, e.g. if the
        // mutex is not locked.
        let current = self.cur.load(Ordering::Relaxed);
        self.prev.store(current, Ordering::Relaxed);

        let _ = unlock();

        match deadline {
            Some(deadline) => {
                crate::sync::futex_wait(&self.cur, current, Some(deadline));
                let _ = lock_with_timeout(deadline);
            }
            None => {
                crate::sync::futex_wait(&self.cur, current, None);
                let _ = lock();
            }
        }
        Ok(())
    }
    pub fn wait(&self, mutex: &Mutex) -> Result<()> {
        self.wait_inner(mutex, None)
    }
}
