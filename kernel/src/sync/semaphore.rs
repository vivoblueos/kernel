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

use super::SpinLock;
use crate::{
    irq, scheduler, scheduler::WaitQueue, thread, thread::Thread, time::WAITING_FOREVER, types::Int,
};
use core::cell::Cell;

#[derive(Debug)]
pub struct Semaphore {
    counter: Cell<Int>,
    // We let the Spinlock protect the whole semaphore.
    pending: SpinLock<WaitQueue>,
}

impl Semaphore {
    pub const fn const_new(counter: Int) -> Self {
        debug_assert!(counter >= 1, "Init resources should not be zero");
        Self {
            counter: Cell::new(counter),
            pending: SpinLock::new(WaitQueue::new()),
        }
    }

    pub const fn new(counter: Int) -> Self {
        Self::const_new(counter)
    }

    pub fn init(&self) -> bool {
        self.pending.irqsave_lock().init()
    }

    pub fn try_acquire(&self) -> bool {
        let w = self.pending.irqsave_lock();
        let old = self.counter.get();
        if old <= 0 {
            return false;
        }
        self.counter.set(old - 1);
        true
    }

    #[inline(never)]
    pub fn acquire_notimeout(&self) -> bool {
        assert!(!irq::is_in_irq());
        let mut w = self.pending.irqsave_lock();
        loop {
            let old = self.counter.get();
            #[cfg(debugging_scheduler)]
            {
                use crate::arch;
                crate::debug!(
                    "[C#{}:0x{:x}] reads counter to acquire: {}",
                    arch::current_cpu_id(),
                    Thread::id(&scheduler::current_thread()),
                    old,
                );
            }
            if old == 0 {
                let _ = scheduler::suspend_me_with_timeout(w, WAITING_FOREVER);
                w = self.pending.irqsave_lock();
                continue;
            } else {
                self.counter.set(old - 1);
                break;
            }
        }
        true
    }

    pub fn acquire_timeout(&self, t: usize) -> bool {
        assert!(!irq::is_in_irq());
        let w = self.pending.irqsave_lock();
        let old = self.counter.get();
        #[cfg(debugging_scheduler)]
        {
            use crate::arch;
            crate::trace!(
                "[TH:0x{:x}] reads counter to acquire: {}",
                scheduler::current_thread_id(),
                old,
            );
        }
        if old == 0 {
            let _ = scheduler::suspend_me_with_timeout(w, t);
            return self.try_acquire();
        } else {
            self.counter.set(old - 1);
        }
        true
    }

    pub fn acquire(&self, timeout: Option<usize>) -> bool {
        let Some(t) = timeout else {
            return self.acquire_notimeout();
        };
        self.acquire_timeout(t)
    }

    #[inline(never)]
    pub fn release(&self) {
        let mut w = self.pending.irqsave_lock();
        let old = self.counter.get();
        #[cfg(debugging_scheduler)]
        {
            use crate::arch;
            crate::trace!(
                "[TH:0x{:x}] reads counter to release: {}",
                scheduler::current_thread_id(),
                old,
            );
        }
        self.counter.set(old + 1);
        if old > 0 {
            return;
        }
        while let Some(next) = w.pop_front() {
            let t = next.thread.clone();
            if let Some(timer) = &t.timer {
                timer.stop();
            }
            let ok = scheduler::queue_ready_thread(thread::SUSPENDED, t);
            if ok {
                break;
            }
            #[cfg(debugging_scheduler)]
            {
                use crate::arch;
                crate::trace!(
                    "[TH:0x{:x}] Failed to enqueue 0x{:x}, state: {}",
                    scheduler::current_thread_id(),
                    Thread::id(&next.thread),
                    next.thread.state()
                );
            }
        }
        drop(w);
        scheduler::yield_me_now_or_later();
    }
}

impl !Send for Semaphore {}
unsafe impl Sync for Semaphore {}

#[cfg(cortex_m)]
#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_semaphore_const_new() {
        // Test successful creation with valid counter
        let semaphore = Semaphore::const_new(5);
        assert_eq!(semaphore.counter.get(), 5);

        // Test creation with minimum valid value
        let semaphore_min = Semaphore::const_new(1);
        assert_eq!(semaphore_min.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_new() {
        // Test that new() calls const_new() correctly
        let semaphore = Semaphore::new(3);
        assert_eq!(semaphore.counter.get(), 3);

        // Test with different values
        let semaphore2 = Semaphore::new(10);
        assert_eq!(semaphore2.counter.get(), 10);
    }

    #[test]
    fn test_semaphore_init() {
        let semaphore = Semaphore::new(2);

        // Test initialization
        let result = semaphore.init();
        assert!(result);

        // Test multiple initializations
        let result2 = semaphore.init();
        assert!(!result2);
    }

    #[test]
    fn test_semaphore_try_acquire_success() {
        let semaphore = Semaphore::new(3);
        semaphore.init();

        // Test successful acquisition
        let result = semaphore.try_acquire();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 2);

        // Test multiple successful acquisitions
        let result2 = semaphore.try_acquire();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 1);

        let result3 = semaphore.try_acquire();
        assert!(result3);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_try_acquire_failure() {
        let semaphore = Semaphore::new(1);
        semaphore.init();

        // Acquire the only available resource
        let result = semaphore.try_acquire();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 0);

        // Try to acquire when counter is 0
        let result2 = semaphore.try_acquire();
        assert!(!result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_notimeout() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Test successful acquisition without timeout
        let result = semaphore.acquire_notimeout();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);

        // Test second acquisition
        let result2 = semaphore.acquire_notimeout();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_timeout_success() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Test successful acquisition with timeout
        let result = semaphore.acquire_timeout(100);
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);

        // Test second acquisition
        let result2 = semaphore.acquire_timeout(100);
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_none() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Test acquire with None timeout (should call acquire_notimeout)
        let result = semaphore.acquire(None);
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_acquire_some() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Test acquire with Some timeout (should call acquire_timeout)
        let result = semaphore.acquire(Some(100));
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_release_basic() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Test basic release
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 3);

        // Test multiple releases
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 4);
    }

    #[test]
    fn test_semaphore_release_after_acquire() {
        let semaphore = Semaphore::new(1);
        semaphore.init();

        // Acquire the resource
        let result = semaphore.try_acquire();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 0);

        // Release the resource
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        // Should be able to acquire again
        let result2 = semaphore.try_acquire();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_release_cycle() {
        let semaphore = Semaphore::new(1);
        semaphore.init();

        // Complete cycle: acquire -> release -> acquire
        let result1 = semaphore.try_acquire();
        assert!(result1);
        assert_eq!(semaphore.counter.get(), 0);

        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        let result2 = semaphore.try_acquire();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_multiple_operations() {
        let semaphore = Semaphore::new(3);
        semaphore.init();

        // Multiple acquire operations
        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 2);

        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 1);

        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 0);

        // Try to acquire when empty
        assert!(!semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 0);

        // Release operations
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        semaphore.release();
        assert_eq!(semaphore.counter.get(), 2);

        // Should be able to acquire again
        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_edge_cases() {
        // Test with maximum value
        let semaphore = Semaphore::new(10);
        semaphore.init();

        // Should be able to acquire
        let result = semaphore.try_acquire();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 9);

        // Test release to maximum
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 10);
    }

    #[test]
    fn test_semaphore_concurrent_simulation() {
        let semaphore = Semaphore::new(2);
        semaphore.init();

        // Simulate concurrent access pattern
        // Thread 1: acquire
        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 1);

        // Thread 2: acquire
        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 0);

        // Thread 3: try to acquire (should fail)
        assert!(!semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 0);

        // Thread 1: release
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        // Thread 3: should be able to acquire now
        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.counter.get(), 0);
    }
}
