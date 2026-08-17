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

use crate::{
    sync::{atomic_wait, atomic_wake},
    time::Tick,
};
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
            let _ = atomic_wait(&self.state, n, Tick::MAX);
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
    const UNITTEST_THREAD_NUM: usize = blueos_kconfig::CONFIG_UNITTEST_THREAD_NUM as usize;

    static_arc! {
        BARRIER(ConstBarrier<2>, ConstBarrier::<{ 2 }>::new()),
    }

    static_arc! {
        BARRIER_MANY(ConstBarrier<{UNITTEST_THREAD_NUM}>, ConstBarrier::<{UNITTEST_THREAD_NUM}>::new()),
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
        for i in 0..UNITTEST_THREAD_NUM - 1 {
            crate::thread::spawn(|| {
                BARRIER_MANY.wait();
            });
        }
        BARRIER_MANY.wait();
    }

    #[test]
    fn join_thread() {
        // Probe phase: exhaust heap with raw blocks (TLSF returns null, proven),
        // then WITHOUT freeing, call Stack::from_size to see if it returns None
        // (null-check works) or returns Some-with-null-stack (null-check missing)
        // or hangs.
        semihosting::println!("[JT] enter n={}", UNITTEST_THREAD_NUM);
        {
            let mut held_raw: alloc::vec::Vec<(*mut u8, core::alloc::Layout)> = alloc::vec::Vec::new();
            let mut k = 0usize;
            loop {
                let layout = core::alloc::Layout::from_size_align(32 * 1024, 8).unwrap();
                let p = unsafe { alloc::alloc::alloc(layout) };
                if p.is_null() {
                    break;
                }
                held_raw.push((p, layout));
                k += 1;
                if k > 64 {
                    break;
                }
            }
            let mi = crate::allocator::memory_info();
            semihosting::println!("[PSE] exhausted k={} used={} total={}", k, mi.used, mi.total);
            // Now heap has ~31KB free. Call Stack::from_size(32768) which needs 32KB.
            semihosting::println!("[PSE] before Stack::from_size");
            let r = crate::thread::Stack::from_size(32 * 1024);
            semihosting::println!("[PSE] after Stack::from_size");
            match r {
                Some(s) => semihosting::println!("[PSE] from_size Some base={:p}", s.base()),
                None => semihosting::println!("[PSE] from_size None"),
            }
            for (p, layout) in held_raw.drain(..) {
                unsafe { alloc::alloc::dealloc(p, layout) };
            }
        }
        // Real test
        let n = UNITTEST_THREAD_NUM;
        let mut vt = Vec::new();
        let counter = Arc::new(AtomicUsize::new(n));
        for i in 0..n {
            let b = Arc::new(ConstBarrier::<{ 2 }>::new());
            vt.push(b.clone());
            let counter = counter.clone();
            let mi = crate::allocator::memory_info();
            semihosting::println!("[JT] pre-spawn i={} used={}", i, mi.used);
            crate::thread::spawn(move || {
                counter.fetch_sub(1, Ordering::Relaxed);
                b.wait();
            });
            semihosting::println!("[JT] spawned i={}", i);
        }
        semihosting::println!("[JT] spawn-done vt.len()={}", vt.len());
        assert_eq!(vt.len(), n);
        let mut idx = 0;
        for b in vt {
            idx += 1;
            b.wait();
        }
        semihosting::println!("[JT] counter={}", counter.load(Ordering::SeqCst));
        assert_eq!(counter.load(Ordering::SeqCst), 0);
    }
}
