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
    error::{code, Error},
    irq, scheduler,
    scheduler::{InsertMode, WaitQueue},
    thread,
    thread::Thread,
    time::WAITING_FOREVER,
    types::ArcList,
};
use bitflags::bitflags;
use core::cell::Cell;
type ThreadList = ArcList<Thread, thread::OffsetOfSchedNode>;

bitflags! {
    #[derive(Default, Debug, Clone, Copy)]
    pub struct EventFlagsMode: u8 {
        const ANY = 1 << 0;
        const ALL = 1 << 1;
        const NO_CLEAR = 1 << 2;
    }
}

#[derive(Debug)]
pub struct EventFlags {
    // We let the Spinlock protect the whole semaphore.
    pending: SpinLock<WaitQueue>,
    flags: Cell<u32>,
}

impl Default for EventFlags {
    fn default() -> Self {
        Self::const_new()
    }
}

impl EventFlags {
    pub const fn const_new() -> Self {
        Self {
            flags: Cell::new(0),
            pending: SpinLock::new(WaitQueue::new()),
        }
    }

    pub fn init(&self, flags: u32) -> bool {
        let mut w = self.pending.irqsave_lock();
        self.flags.set(flags);
        w.init()
    }

    pub fn set(&self, flags: u32) -> Result<u32, Error> {
        if flags == 0 {
            return Err(code::EINVAL);
        }

        let mut thread_list = ThreadList::new();
        thread_list.init();

        let mut w = self.pending.irqsave_lock();
        let new_flags = self.flags.get() | flags;
        for mut entry in w.iter() {
            let mut thread = entry.thread.clone();
            let event_mask = thread.event_flags_mask();
            let event_mode = thread.event_flags_mode();
            if event_mode.contains(EventFlagsMode::ANY)
                && (event_mask & flags != 0 || event_mask == 0)
                || event_mode.contains(EventFlagsMode::ALL) && event_mask & flags == event_mask
            {
                WaitQueue::detach(&mut entry);
                thread_list.push_back(thread);
            }
        }

        let need_schedule = !thread_list.is_empty();
        let mut clear_flags = 0;
        while let Some(thread) = thread_list.pop_front() {
            if let Some(timer) = &thread.timer {
                timer.stop();
            }
            if !thread.event_flags_mode().contains(EventFlagsMode::NO_CLEAR) {
                clear_flags |= thread.event_flags_mask();
            }
            scheduler::queue_ready_thread(thread::SUSPENDED, thread);
        }

        let new_flags = if clear_flags != 0 {
            new_flags & !clear_flags
        } else {
            new_flags
        };
        self.flags.set(new_flags);
        drop(w);

        if need_schedule {
            scheduler::yield_me_now_or_later();
        }

        Ok(new_flags)
    }

    pub fn clear(&self, flags: u32) -> u32 {
        let mut w = self.pending.irqsave_lock();
        let old_flags = self.flags.get();
        self.flags.set(old_flags & !flags);
        old_flags
    }

    pub fn get(&self) -> u32 {
        let _guard = self.pending.irqsave_lock();
        self.flags.get()
    }

    pub fn wait(&self, flags: u32, mode: EventFlagsMode, timeout: usize) -> Result<u32, Error> {
        if flags == 0 && mode.contains(EventFlagsMode::ALL) {
            return Err(code::EINVAL);
        }

        let mut w = self.pending.irqsave_lock();
        let mut event_get = false;
        let event_flags = self.flags.get();
        if mode.contains(EventFlagsMode::ANY) {
            if event_flags & flags != 0 || flags == 0 && event_flags != 0 {
                event_get = true;
            }
        } else if mode.contains(EventFlagsMode::ALL) && event_flags & flags == flags {
            event_get = true;
        }

        let current_thread = scheduler::current_thread();
        if event_get {
            {
                let mut locked_thread = current_thread.lock();
                locked_thread.set_event_flags_mask(event_flags & flags);
                locked_thread.set_event_flags_mode(mode);
            }
            if !mode.contains(EventFlagsMode::NO_CLEAR) {
                self.flags.set(event_flags & !flags);
            }
            return Ok(event_flags);
        }

        if timeout == 0 {
            return Err(code::ETIMEDOUT);
        }

        {
            let mut locked_thread = current_thread.lock();
            locked_thread.set_event_flags_mask(flags);
            locked_thread.set_event_flags_mode(mode);
        }
        let timed_out = scheduler::suspend_me_with_timeout(w, timeout, InsertMode::InsertToEnd);
        if timed_out {
            return Err(code::ETIMEDOUT);
        }

        // The flags are cleared by the thread when it is resumed.
        Ok(event_flags)
    }

    pub fn reset(&self) {
        let mut w = self.pending.irqsave_lock();
        self.flags.set(0);
        while let Some(entry) = w.pop_front() {
            let thread = entry.thread.clone();
            if let Some(timer) = &thread.timer {
                timer.stop();
            }
            scheduler::queue_ready_thread(thread::SUSPENDED, thread);
        }
        drop(w);
        scheduler::yield_me_now_or_later();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_event_flags_const_new() {
        let event_flags = EventFlags::const_new();
        assert_eq!(event_flags.get(), 0);
    }

    #[test]
    fn test_event_flags_init() {
        let event_flags = EventFlags::const_new();
        assert!(event_flags.init(0));
    }

    #[test]
    fn test_event_flags_set_get() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Test set and get single flag
        assert!(event_flags.set(0x01).is_ok());
        assert_eq!(event_flags.get(), 0x01);

        // Test set multiple flags
        assert!(event_flags.set(0x02).is_ok());
        assert_eq!(event_flags.get(), 0x03); // 0x01 | 0x02

        // Test clear
        event_flags.clear(0x01);
        assert_eq!(event_flags.get(), 0x02);
    }

    #[test]
    fn test_event_flags_set_zero() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Setting zero flags should return error
        assert_eq!(event_flags.set(0), Err(code::EINVAL));
    }

    #[test]
    fn test_event_flags_wait_any() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set flags first
        assert!(event_flags.set(0x01).is_ok());

        // Wait for any flag (should succeed immediately)
        let result = event_flags.wait(0x01, EventFlagsMode::ANY, 100);
        assert!(result.is_ok());

        // Wait for flag that doesn't exist (should timeout)
        let result = event_flags.wait(0x02, EventFlagsMode::ANY, 100);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_event_flags_wait_all() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set multiple flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());

        // Wait for all flags (should succeed)
        let result = event_flags.wait(0x03, EventFlagsMode::ALL, 100);
        assert!(result.is_ok());

        // Wait for flags that don't all exist (should timeout)
        let result = event_flags.wait(0x07, EventFlagsMode::ALL, 100);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_event_flags_wait_zero() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Waiting for zero flags should return error
        let result = event_flags.wait(0, EventFlagsMode::ALL, 100);
        assert_eq!(result, Err(code::EINVAL));

        let result = event_flags.wait(0, EventFlagsMode::ANY, 0);
        assert_eq!(result, Err(code::ETIMEDOUT));

        let result = event_flags.wait(0, EventFlagsMode::ANY, 100);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_event_flags_timeout() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Wait with zero timeout should return error immediately
        let result = event_flags.wait(0x01, EventFlagsMode::ANY, 0);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_event_flags_no_clear() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set flags
        assert!(event_flags.set(0x01).is_ok());
        assert_eq!(event_flags.get(), 0x01);

        // Wait with NO_CLEAR mode
        let result = event_flags.wait(0x01, EventFlagsMode::ANY | EventFlagsMode::NO_CLEAR, 100);
        assert!(result.is_ok());

        // Flags should still be set
        assert_eq!(event_flags.get(), 0x01);
    }

    #[test]
    fn test_event_flags_clear_on_wait() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set flags
        assert!(event_flags.set(0x01).is_ok());
        assert_eq!(event_flags.get(), 0x01);

        // Wait without NO_CLEAR mode
        let result = event_flags.wait(0x01, EventFlagsMode::ANY, 1000);
        assert!(result.is_ok());

        // Flags should be cleared
        assert_eq!(event_flags.get(), 0x00);
    }

    #[test]
    fn test_event_flags_edge_cases() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Test with maximum flag values
        assert!(event_flags.set(0xFFFFFFFF).is_ok());
        assert_eq!(event_flags.get(), 0xFFFFFFFF);

        // Test clear with maximum value
        event_flags.clear(0xFFFFFFFF);
        assert_eq!(event_flags.get(), 0x00);

        // Test set with single bit flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert!(event_flags.set(0x04).is_ok());
        assert!(event_flags.set(0x08).is_ok());
        assert_eq!(event_flags.get(), 0x0F);

        // Test clear with partial bits
        event_flags.clear(0x05); // Clear 0x01 and 0x04
        assert_eq!(event_flags.get(), 0x0A); // 0x02 and 0x08 remain
    }

    #[test]
    fn test_event_flags_wait_combinations() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set multiple flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert!(event_flags.set(0x04).is_ok());
        assert_eq!(event_flags.get(), 0x07);

        // Wait for ANY with multiple flags set
        assert!(event_flags.wait(0x01, EventFlagsMode::ANY, 100).is_ok());
        assert_eq!(event_flags.get(), 0x06); // 0x02 and 0x04 remain

        // Wait for ALL with remaining flags
        assert!(event_flags.wait(0x06, EventFlagsMode::ALL, 100).is_ok());
        assert_eq!(event_flags.get(), 0x00); // All cleared
    }

    #[test]
    fn test_event_flags_no_clear_behavior() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Set flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert_eq!(event_flags.get(), 0x03);

        // Wait with NO_CLEAR for ANY
        assert!(event_flags
            .wait(0x01, EventFlagsMode::ANY | EventFlagsMode::NO_CLEAR, 100)
            .is_ok());
        assert_eq!(event_flags.get(), 0x03); // Should not be cleared

        // Wait with NO_CLEAR for ALL
        assert!(event_flags
            .wait(0x03, EventFlagsMode::ALL | EventFlagsMode::NO_CLEAR, 100)
            .is_ok());
        assert_eq!(event_flags.get(), 0x03); // Should not be cleared

        // Manual clear
        event_flags.clear(0x03);
        assert_eq!(event_flags.get(), 0x00);
    }

    #[test]
    fn test_event_flags_complex_scenario() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Test complex scenario with multiple operations
        assert!(event_flags.set(0x01).is_ok());
        assert_eq!(event_flags.get(), 0x01);

        // Wait for any flag
        assert!(event_flags.wait(0x01, EventFlagsMode::ANY, 100).is_ok());
        assert_eq!(event_flags.get(), 0x00); // Should be cleared

        // Set multiple flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert!(event_flags.set(0x04).is_ok());
        assert_eq!(event_flags.get(), 0x07);

        // Wait for specific combination
        assert!(event_flags.wait(0x03, EventFlagsMode::ALL, 100).is_ok());
        assert_eq!(event_flags.get(), 0x04); // Only 0x04 should remain

        // Clear remaining flag
        event_flags.clear(0x04);
        assert_eq!(event_flags.get(), 0x00);
    }

    #[test]
    fn test_event_flags_mode_combinations() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Test ANY + NO_CLEAR
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags
            .wait(0x01, EventFlagsMode::ANY | EventFlagsMode::NO_CLEAR, 100)
            .is_ok());
        assert_eq!(event_flags.get(), 0x01); // Should not be cleared

        // Test ALL + NO_CLEAR
        assert!(event_flags.set(0x02).is_ok());
        assert!(event_flags
            .wait(0x03, EventFlagsMode::ALL | EventFlagsMode::NO_CLEAR, 100)
            .is_ok());
        assert_eq!(event_flags.get(), 0x03); // Should not be cleared

        // Clear manually
        event_flags.clear(0x03);
        assert_eq!(event_flags.get(), 0x00);
    }

    #[test]
    fn test_event_flags_mode_constants() {
        // Test EventFlagsMode constants
        assert_eq!(EventFlagsMode::ANY.bits(), 1);
        assert_eq!(EventFlagsMode::ALL.bits(), 2);
        assert_eq!(EventFlagsMode::NO_CLEAR.bits(), 4);

        // Test combinations
        let any_all = EventFlagsMode::ANY | EventFlagsMode::ALL;
        assert_eq!(any_all.bits(), 3);

        let any_no_clear = EventFlagsMode::ANY | EventFlagsMode::NO_CLEAR;
        assert_eq!(any_no_clear.bits(), 5);

        let all_no_clear = EventFlagsMode::ALL | EventFlagsMode::NO_CLEAR;
        assert_eq!(all_no_clear.bits(), 6);

        let all_combined = EventFlagsMode::ANY | EventFlagsMode::ALL | EventFlagsMode::NO_CLEAR;
        assert_eq!(all_combined.bits(), 7);
    }

    #[test]
    fn test_event_flags_sequential_operations() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Sequential set operations
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert!(event_flags.set(0x04).is_ok());
        assert!(event_flags.set(0x08).is_ok());
        assert_eq!(event_flags.get(), 0x0F);

        // Sequential clear operations
        event_flags.clear(0x01);
        assert_eq!(event_flags.get(), 0x0E);
        event_flags.clear(0x02);
        assert_eq!(event_flags.get(), 0x0C);
        event_flags.clear(0x04);
        assert_eq!(event_flags.get(), 0x08);
        event_flags.clear(0x08);
        assert_eq!(event_flags.get(), 0x00);
    }

    #[test]
    fn test_event_flags_clear_nonexistent() {
        let event_flags = EventFlags::const_new();
        event_flags.init(0);

        // Clear flags that don't exist (should be safe)
        event_flags.clear(0x01);
        assert_eq!(event_flags.get(), 0x00);

        // Set some flags
        assert!(event_flags.set(0x01).is_ok());
        assert!(event_flags.set(0x02).is_ok());
        assert_eq!(event_flags.get(), 0x03);

        // Clear flags that partially exist
        event_flags.clear(0x05); // Clear 0x01 and 0x04 (0x04 doesn't exist)
        assert_eq!(event_flags.get(), 0x02); // Only 0x02 remains
    }
}
