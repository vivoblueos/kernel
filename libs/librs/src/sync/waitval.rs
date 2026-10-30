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

#[derive(Debug)]
pub struct Waitval<T> {
    state: AtomicUsize,
    value: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T: Send + Sync> Send for Waitval<T> {}
unsafe impl<T: Send + Sync> Sync for Waitval<T> {}

impl<T> Waitval<T> {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(0),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    // SAFETY: Caller must ensure both (1) that the value has not yet been initialized, and (2)
    // that this is never run by more than one thread simultaneously.
    pub fn post(&self, value: T) {
        unsafe { self.value.get().write(MaybeUninit::new(value)) };
        self.state.store(1, Ordering::Release);
        crate::sync::futex_wake(&self.state, usize::MAX);
    }

    pub fn wait(&self) -> &T {
        while self.state.load(Ordering::Acquire) == 0 {
            crate::sync::futex_wait(&self.state, 0, None);
        }

        unsafe { (*self.value.get()).assume_init_ref() }
    }
}
