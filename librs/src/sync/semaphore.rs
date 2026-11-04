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

use core::sync::atomic::{AtomicUsize, Ordering};

/// A counting semaphore.
///
/// `#[repr(C)]` because this type *is* the C library's `sem_t`: a C caller
/// allocates the object and the kernel casts the pointer to this type.
#[repr(C)]
pub struct Semaphore {
    count: AtomicUsize,
}

impl Semaphore {
    pub const fn new(value: usize) -> Self {
        Self {
            count: AtomicUsize::new(value),
        }
    }

    // TODO: Acquire-Release ordering?

    pub fn post(&self, count: usize) {
        self.count.fetch_add(count, Ordering::SeqCst);
        // TODO: notify one?
        crate::sync::futex_wake(&self.count, usize::MAX);
    }

    /// Decrements the semaphore if it is non-zero.
    ///
    /// Returns `true` if the semaphore was acquired, `false` if it was
    /// exhausted (which is what POSIX reports as `EAGAIN`).
    pub fn try_wait(&self) -> bool {
        loop {
            let value = self.count.load(Ordering::SeqCst);

            if value == 0 {
                return false;
            }

            if self
                .count
                .compare_exchange_weak(value, value - 1, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                // Acquired
                return true;
            }

            // Try again (as long as value > 0)
        }
    }

    /// Waits for the semaphore.
    ///
    /// With `timeout` given, the wait gives up at that **absolute** deadline
    /// and returns `false`; otherwise it blocks indefinitely.
    pub fn wait(&self, timeout: Option<&crate::time::deadline::Deadline>) -> bool {
        match timeout {
            Some(deadline) => self.wait_until(deadline),
            None => loop {
                if self.try_wait() {
                    // Acquired.
                    return true;
                }
                // Use futex to wait for the next change, without a timeout.
                crate::sync::futex_wait(&self.count, 0, None);
            },
        }
    }
    /// Waits for the semaphore, giving up at `deadline`.
    ///
    /// `deadline` is an **absolute** time on a specific clock, matching the
    /// POSIX contract of `sem_timedwait` and the Issue 8 `sem_clockwait`.
    /// Returns `true` if the semaphore was acquired, `false` on timeout.
    pub fn wait_until(&self, deadline: &crate::time::deadline::Deadline) -> bool {
        loop {
            if self.try_wait() {
                // Acquired.
                return true;
            }

            match crate::sync::futex_wait_until(&self.count, 0, deadline) {
                // Woken up: re-check the count.
                Ok(true) => continue,
                // The deadline expired.
                Ok(false) => return false,
                // A hard error (EAGAIN for a stale value) still means the
                // count may have changed, so re-check it.
                Err(_) => continue,
            }
        }
    }

    pub fn value(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}
