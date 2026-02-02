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
    irq, scheduler,
    scheduler::{wait_queue, InsertMode, InsertModeTrait, WaitEntry, WaitQueue},
    thread,
    thread::Thread,
    time::Tick,
    types::Uint,
};
use core::{cell::Cell, ops::DerefMut};

#[derive(Debug)]
pub struct Semaphore {
    counter: Cell<Uint>,
    // We let the Spinlock protect the whole semaphore.
    pending: SpinLock<WaitQueue>,
}

impl Semaphore {
    pub const fn new() -> Self {
        Self {
            counter: Cell::new(1),
            pending: SpinLock::new(WaitQueue::new()),
        }
    }

    pub fn init(&self, counter: Uint) -> bool {
        let mut w = self.pending.irqsave_lock();
        self.counter.set(counter);
        w.init()
    }

    pub fn count(&self) -> Uint {
        let _w = self.pending.irqsave_lock();
        self.counter.get()
    }

    #[inline(always)]
    pub fn try_acquire<M>(&self) -> bool
    where
        M: InsertModeTrait,
    {
        self.acquire_timeout::<M>(Tick(0))
    }

    pub fn try_acquire_nowait(&self) -> bool {
        let Some(w) = self.pending.try_irqsave_lock() else {
            return false;
        };
        let old = self.counter.get();
        if old == 0 {
            return false;
        }
        self.counter.set(old - 1);
        true
    }

    pub fn acquire_notimeout<M>(&self) -> bool
    where
        M: InsertModeTrait,
    {
        debug_assert!(!irq::is_in_irq());
        let this_thread = scheduler::current_thread();
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
            if old != 0 {
                self.counter.set(old - 1);
                return true;
            }
            let mut borrowed_wait_entry;
            {
                let mut wait_entry = WaitEntry::new(this_thread.clone());
                borrowed_wait_entry =
                    wait_queue::insert(w.deref_mut(), &mut wait_entry, M::MODE).unwrap();
                let timeout = scheduler::suspend_me_for(Tick::MAX, Some(w));
                debug_assert!(!timeout);
                w = self.pending.irqsave_lock();
                borrowed_wait_entry = w.pop(borrowed_wait_entry).unwrap();
            }
            drop(borrowed_wait_entry);
        }
    }

    pub fn acquire_timeout<M>(&self, mut ticks: Tick) -> bool
    where
        M: InsertModeTrait,
    {
        debug_assert!(!irq::is_in_irq());
        let this_thread = scheduler::current_thread();
        let mut w = self.pending.irqsave_lock();
        let mut last_sys_ticks = Tick::now();
        loop {
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
            if old != 0 {
                self.counter.set(old - 1);
                return true;
            }
            // Don't bother to suspend further.
            if ticks.0 == 0 {
                return false;
            }
            let mut borrowed_wait_entry;
            {
                let mut wait_entry = WaitEntry::new(this_thread.clone());
                borrowed_wait_entry =
                    wait_queue::insert(w.deref_mut(), &mut wait_entry, M::MODE).unwrap();
                let timeout = scheduler::suspend_me_for(ticks, Some(w));
                w = self.pending.irqsave_lock();
                borrowed_wait_entry = w.pop(borrowed_wait_entry).unwrap();
                if timeout {
                    return false;
                }
            }
            drop(borrowed_wait_entry);
            if ticks == Tick::MAX {
                continue;
            }
            let now = Tick::now();
            let elapsed_ticks = now.0 - last_sys_ticks.0;
            if elapsed_ticks >= ticks.0 {
                ticks = Tick(0);
            } else {
                ticks.0 -= elapsed_ticks;
            }
            last_sys_ticks = now;
        }
    }

    pub fn acquire<M>(&self, timeout: Tick) -> bool
    where
        M: InsertModeTrait,
    {
        if timeout.0 == 0 {
            return self.acquire_notimeout::<M>();
        };
        self.acquire_timeout::<M>(timeout)
    }

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
        for next in w.iter() {
            let t = next.thread.clone();
            if scheduler::queue_ready_thread(thread::SUSPENDED, t).is_ok() {
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

    pub fn reset(&self) -> usize {
        let mut w = self.pending.irqsave_lock();
        self.counter.set(0);
        // Wakeup all threads.
        scheduler::wake_up_all(w)
    }
}

impl !Send for Semaphore {}
unsafe impl Sync for Semaphore {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scheduler::{InsertByPrio, InsertMode, InsertToEnd};
    use blueos_test_macro::test;

    #[test]
    fn test_semaphore_init() {
        let semaphore = Semaphore::new();

        // Test initialization
        let result = semaphore.init(2);
        assert!(result);
        assert_eq!(semaphore.counter.get(), 2);

        // Test multiple initializations
        let result2 = semaphore.init(3);
        assert!(!result2);
    }

    #[test]
    fn test_semaphore_count() {
        let semaphore = Semaphore::new();
        semaphore.init(5);

        // Test semaphore number count
        assert_eq!(semaphore.count(), 5);
    }

    #[test]
    fn test_semaphore_try_acquire_success() {
        let semaphore = Semaphore::new();
        semaphore.init(3);

        // Test successful acquisition
        let result = semaphore.try_acquire::<InsertToEnd>();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 2);

        // Test multiple successful acquisitions
        let result2 = semaphore.try_acquire::<InsertToEnd>();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 1);

        let result3 = semaphore.try_acquire::<InsertToEnd>();
        assert!(result3);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_try_acquire_failure() {
        let semaphore = Semaphore::new();
        semaphore.init(1);

        // Acquire the only available resource
        let result = semaphore.try_acquire::<InsertToEnd>();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 0);

        // Try to acquire when counter is 0
        let result2 = semaphore.try_acquire::<InsertToEnd>();
        assert!(!result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_notimeout() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Test successful acquisition without timeout
        let result = semaphore.acquire_notimeout::<InsertToEnd>();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);

        // Test second acquisition
        let result2 = semaphore.acquire_notimeout::<InsertToEnd>();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_timeout_success() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Test successful acquisition with timeout
        let result = semaphore.acquire_timeout::<InsertToEnd>(Tick(100));
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);

        // Test second acquisition
        let result2 = semaphore.acquire_timeout::<InsertToEnd>(Tick(100));
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_none() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Test acquire with None timeout (should call acquire_notimeout)
        let result = semaphore.acquire::<InsertToEnd>(Tick::MAX);
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_acquire_some() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Test acquire with Some timeout (should call acquire_timeout)
        let result = semaphore.acquire::<InsertToEnd>(Tick(100));
        assert!(result);
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_release_basic() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Test basic release
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 3);

        // Test multiple releases
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 4);
    }

    #[test]
    fn test_semaphore_release_after_acquire() {
        let semaphore = Semaphore::new();
        semaphore.init(1);

        // Acquire the resource
        let result = semaphore.try_acquire::<InsertToEnd>();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 0);

        // Release the resource
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        // Should be able to acquire again
        let result2 = semaphore.try_acquire::<InsertToEnd>();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_acquire_release_cycle() {
        let semaphore = Semaphore::new();
        semaphore.init(1);

        // Complete cycle: acquire -> release -> acquire
        let result1 = semaphore.try_acquire::<InsertToEnd>();
        assert!(result1);
        assert_eq!(semaphore.counter.get(), 0);

        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        let result2 = semaphore.try_acquire::<InsertToEnd>();
        assert!(result2);
        assert_eq!(semaphore.counter.get(), 0);
    }

    #[test]
    fn test_semaphore_multiple_operations() {
        let semaphore = Semaphore::new();
        semaphore.init(3);

        // Multiple acquire operations
        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 2);

        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 1);

        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 0);

        // Try to acquire when empty
        assert!(!semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 0);

        // Release operations
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        semaphore.release();
        assert_eq!(semaphore.counter.get(), 2);

        // Should be able to acquire again
        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 1);
    }

    #[test]
    fn test_semaphore_edge_cases() {
        // Test with maximum value
        let semaphore = Semaphore::new();
        semaphore.init(10);

        // Should be able to acquire
        let result = semaphore.try_acquire::<InsertToEnd>();
        assert!(result);
        assert_eq!(semaphore.counter.get(), 9);

        // Test release to maximum
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 10);
    }

    #[test]
    fn test_semaphore_concurrent_simulation() {
        let semaphore = Semaphore::new();
        semaphore.init(2);

        // Simulate concurrent access pattern
        // Thread 1: acquire
        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 1);

        // Thread 2: acquire
        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 0);

        // Thread 3: try to acquire (should fail)
        assert!(!semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 0);

        // Thread 1: release
        semaphore.release();
        assert_eq!(semaphore.counter.get(), 1);

        // Thread 3: should be able to acquire now
        assert!(semaphore.try_acquire::<InsertToEnd>());
        assert_eq!(semaphore.counter.get(), 0);
    }
}
