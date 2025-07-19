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
    cell::UnsafeCell,
    mem::MaybeUninit,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::AttemptStatus;

const UNINITIALIZED: usize = 0;
const INITIALIZING: usize = 1;
const WAITING: usize = 2;
const INITIALIZED: usize = 3;

pub struct Once<T> {
    status: AtomicUsize,
    data: UnsafeCell<MaybeUninit<T>>,
}

// SAFETY:
//
// Sending a Once is the same as sending a (wrapped) T.
unsafe impl<T: Send> Send for Once<T> {}

// SAFETY:
//
// For Once to be shared between threads without being unsound, only call_once needs to be safe, at
// the moment.
//
// Send requirement: the thread that gets to run the initializer function, will put a T in the cell
// which can then be accessed by other threads, thus T needs to be send.
//
// Sync requirement: after call_once has been called, it returns the value via &T, which naturally
// forces T to be Sync.
unsafe impl<T: Send + Sync> Sync for Once<T> {}

impl<T> Once<T> {
    pub const fn new() -> Self {
        Self {
            status: AtomicUsize::new(UNINITIALIZED),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }
    pub fn call_once(&self, constructor: impl FnOnce() -> T) -> &T {
        match self.status.compare_exchange(
            UNINITIALIZED,
            INITIALIZING,
            // SAFETY: Success ordering: if the CAS succeeds, we technically need no
            // synchronization besides the Release store to INITIALIZED, and Acquire here forbids
            // possible loads in f() to be re-ordered before this CAS. One could argue whether or
            // not that is reasonable, but the main point is that the success ordering must be at
            // least as strong as the failure ordering.
            Ordering::Acquire,
            // SAFETY: Failure ordering: if the CAS fails, and status was INITIALIZING | WAITING,
            // then Relaxed is sufficient, as it will have to be Acquire-loaded again later. If
            // INITIALIZED is encountered however, it will nonatomically read the value in the
            // Cell, which necessitates Acquire.
            Ordering::Acquire, // TODO: On archs where this matters, use Relaxed and core::sync::atomic::fence?
        ) {
            Ok(_must_be_uninit) => {
                // We now have exclusive access to the cell, let's initiate things!
                unsafe { self.data.get().cast::<T>().write(constructor()) };

                // Mark the data as initialized
                if self.status.swap(INITIALIZED, Ordering::Release) == WAITING {
                    // At least one thread is waiting on this to finish
                    crate::sync::futex_wake(&self.status, usize::MAX);
                }
            }
            Err(INITIALIZING) | Err(WAITING) => crate::sync::wait_until_generic(
                &self.status,
                // SAFETY: An Acquire load is necessary for the nonatomic store by the thread
                // running the constructor, to become visible.
                |status| match status.load(Ordering::Acquire) {
                    WAITING => AttemptStatus::Waiting,
                    INITIALIZED => AttemptStatus::Desired,
                    _ => AttemptStatus::Other,
                },
                // SAFETY: Double-Acquire is necessary here as well, because if the CAS fails and
                // it was INITIALIZED, the nonatomic write by the constructor thread, must be
                // visible.
                |status| match status
                    .compare_exchange_weak(
                        INITIALIZING,
                        WAITING,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    )
                    .unwrap_or_else(|e| e)
                {
                    WAITING => AttemptStatus::Waiting,
                    INITIALIZED => AttemptStatus::Desired,
                    _ => AttemptStatus::Other,
                },
                WAITING,
            ),
            Err(INITIALIZED) => (),

            // TODO: Only for debug builds?
            Err(_) => unreachable!("invalid state for Once<T>"),
        }

        // At this point the data must be initialized!
        unsafe { (*self.data.get()).assume_init_ref() }
    }
}

impl<T> Default for Once<T> {
    fn default() -> Self {
        Self::new()
    }
}
