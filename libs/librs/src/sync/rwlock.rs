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

use super::futex_wait;
use libc::{c_int, timespec};

pub(crate) struct Rwlock {
    state: AtomicUsize,
}

const WAITING_WR: usize = 1 << (usize::BITS - 1);
const COUNT_MASK: usize = WAITING_WR - 1;
const EXCLUSIVE: usize = COUNT_MASK;

impl Rwlock {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(0),
        }
    }

    pub fn acquire_write_lock(&self, deadline: Option<&timespec>) {
        let mut waiting_wr = self.state.load(Ordering::Relaxed) & WAITING_WR;

        loop {
            match self.state.compare_exchange_weak(
                waiting_wr,
                EXCLUSIVE,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(actual) => {
                    let expected = if actual & COUNT_MASK != EXCLUSIVE {
                        // Set the exclusive bit, but only if we're waiting for readers, to avoid
                        // reader starvation by overprioritizing write locks.
                        self.state.fetch_or(WAITING_WR, Ordering::Relaxed);

                        actual | WAITING_WR
                    } else {
                        actual
                    };
                    waiting_wr = expected & WAITING_WR;

                    if actual & COUNT_MASK > 0 {
                        let _ = futex_wait(&self.state, expected, deadline);
                    } else {
                        // We must avoid blocking indefinitely in our `futex_wait()`, in this case
                        // where it's possible that `self.state == expected` but our futex might
                        // never be woken again, because it's possible that all other threads
                        // already did their `futex_wake()` before we would've done our
                        // `futex_wait()`.
                    }
                }
            }
        }
    }

    pub fn acquire_read_lock(&self, deadline: Option<&timespec>) {
        // TODO: timeout
        while let Err(old) = self.try_acquire_read_lock() {
            crate::sync::futex_wait(&self.state, old, deadline);
        }
    }

    pub fn try_acquire_read_lock(&self) -> Result<(), usize> {
        let mut cached = self.state.load(Ordering::Acquire);

        loop {
            let waiting_wr = cached & WAITING_WR;
            let old = if cached & COUNT_MASK == EXCLUSIVE {
                0
            } else {
                cached & COUNT_MASK
            };
            let new = old + 1;

            // TODO: Return with error code instead?
            assert_ne!(
                new & COUNT_MASK,
                EXCLUSIVE,
                "maximum number of rwlock readers reached"
            );

            match self.state.compare_exchange_weak(
                (old & COUNT_MASK) | waiting_wr,
                new | waiting_wr,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(()),

                Err(value) if value & COUNT_MASK == EXCLUSIVE => return Err(value),
                Err(value) => {
                    cached = value;
                    // TODO: SCHED_YIELD?
                    core::hint::spin_loop();
                }
            }
        }
    }

    pub fn try_acquire_write_lock(&self) -> Result<(), usize> {
        let mut waiting_wr = self.state.load(Ordering::Relaxed) & WAITING_WR;

        loop {
            match self.state.compare_exchange_weak(
                waiting_wr,
                EXCLUSIVE,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(()),
                Err(actual) if actual & COUNT_MASK > 0 => return Err(actual),
                Err(can_retry) => {
                    waiting_wr = can_retry & WAITING_WR;

                    core::hint::spin_loop();
                    continue;
                }
            }
        }
    }

    pub fn unlock(&self) {
        let state = self.state.load(Ordering::Relaxed);

        if state & COUNT_MASK == EXCLUSIVE {
            // Unlocking a write lock.
            // This discards the writer-waiting bit, in order to ensure some level of fairness
            // between read and write locks.
            self.state.store(0, Ordering::Release);
            let _ = crate::sync::futex_wake(&self.state, usize::MAX);
        } else {
            // Unlocking a read lock. Subtract one from the reader count, but preserve the
            // WAITING_WR bit.
            if self.state.fetch_sub(1, Ordering::Release) & COUNT_MASK == 1 {
                let _ = crate::sync::futex_wake(&self.state, usize::MAX);
            }
        }
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub enum Pshared {
    #[default]
    Private,

    Shared,
}
impl Pshared {
    pub const fn from_raw(raw: c_int) -> Option<Self> {
        Some(match raw {
            crate::pthread::PTHREAD_PROCESS_PRIVATE => Self::Private,
            crate::pthread::PTHREAD_PROCESS_SHARED => Self::Shared,

            _ => return None,
        })
    }
    pub const fn raw(self) -> c_int {
        match self {
            Self::Private => crate::pthread::PTHREAD_PROCESS_PRIVATE,
            Self::Shared => crate::pthread::PTHREAD_PROCESS_SHARED,
        }
    }
}

#[derive(Clone, Copy, Default)]
pub(crate) struct RwlockAttr {
    pub pshared: Pshared,
}
