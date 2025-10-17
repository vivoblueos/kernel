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

// Similar to std::sync::Barrier.

use crate::sync::{atomic_wait, atomic_wake};
use core::sync::atomic::{AtomicUsize, Ordering};

// Used when N is small and contention is low.
#[derive(Debug, Default)]
pub struct ConstBarrier<const N: usize> {
    state: AtomicUsize,
}

impl<const N: usize> ConstBarrier<N> {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(0),
        }
    }

    pub fn wait(&self) {
        let mut n = self.state.fetch_add(1, Ordering::Release) + 1;
        if n == N {
            let _ = atomic_wake(&self.state, n - 1);
            return;
        }
        loop {
            let _ = atomic_wait(&self.state, n, None);
            n = self.state.load(Ordering::Acquire);
            if n == N {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{static_arc, types::Arc};
    use alloc::vec::Vec;
    use blueos_test_macro::test;

    static_arc! {
        BARRIER(ConstBarrier<2>, ConstBarrier::<{ 2 }>::new()),
    }

    static_arc! {
        BARRIER_MANY(ConstBarrier<64>, ConstBarrier::<{ 64 }>::new()),
    }

    #[test]
    fn test_barrier_basic() {
        crate::thread::spawn(|| {
            BARRIER.wait();
        });
        BARRIER.wait();
    }

    // Should not hang.
    #[test]
    fn stress_barrier() {
        for i in 0..63 {
            crate::thread::spawn(|| {
                BARRIER_MANY.wait();
            });
        }
        BARRIER_MANY.wait();
    }

    #[test]
    fn join_thread() {
        let n = 64;
        let mut vt = Vec::new();
        let counter = Arc::new(AtomicUsize::new(n));
        for i in 0..n {
            let b = Arc::new(ConstBarrier::<{ 2 }>::new());
            vt.push(b.clone());
            let counter = counter.clone();
            crate::thread::spawn(move || {
                counter.fetch_sub(1, Ordering::Relaxed);
                b.wait();
            });
        }
        assert_eq!(vt.len(), n);
        for b in vt {
            b.wait();
        }
        assert_eq!(counter.load(Ordering::SeqCst), 0);
    }
}
