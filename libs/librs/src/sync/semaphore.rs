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

use crate::time::clock_gettime;
use core::sync::atomic::{AtomicUsize, Ordering};
use libc::{timespec, CLOCK_MONOTONIC};

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

    pub fn try_wait(&self) -> usize {
        loop {
            let value = self.count.load(Ordering::SeqCst);

            if value == 0 {
                return 0;
            }

            if self
                .count
                .compare_exchange_weak(value, value - 1, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                // Acquired
                return value;
            }

            // Try again (as long as value > 0)
        }
    }

    pub fn wait(&self, timeout_opt: Option<&timespec>) -> bool {
        loop {
            let value = self.try_wait();

            if value == 0 {
                return true;
            }

            if let Some(timeout) = timeout_opt {
                let mut time = timespec {
                    tv_sec: 0,
                    tv_nsec: 0,
                };
                unsafe { clock_gettime(CLOCK_MONOTONIC, &mut time) };
                if (time.tv_sec > timeout.tv_sec)
                    || (time.tv_sec == timeout.tv_sec && time.tv_nsec >= timeout.tv_nsec)
                {
                    //Timeout happened, return error
                    return false;
                } else {
                    // Use futex to wait for the next change, with a relative timeout
                    let mut relative = timespec {
                        tv_sec: timeout.tv_sec,
                        tv_nsec: timeout.tv_nsec,
                    };
                    while relative.tv_nsec < time.tv_nsec {
                        relative.tv_sec -= 1;
                        relative.tv_nsec += 1_000_000_000;
                    }
                    relative.tv_sec -= time.tv_sec;
                    relative.tv_nsec -= time.tv_nsec;

                    crate::sync::futex_wait(&self.count, value, Some(&relative));
                }
            } else {
                // Use futex to wait for the next change, without a timeout
                crate::sync::futex_wait(&self.count, value, None);
            }
        }
    }
    pub fn value(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}
