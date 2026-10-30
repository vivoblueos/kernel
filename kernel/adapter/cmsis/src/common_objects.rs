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

extern crate alloc;
use crate::{os_adapter, MAX_NAME_LEN};
#[cfg(event_flags)]
use blueos::sync::event_flags::EventFlagsMode;
use blueos::{
    error::Error,
    scheduler::{self, InsertModeTrait},
    sync::{mqueue::SendMode, SpinLockGuard},
    thread,
    time::Tick,
    types::{Arc, ThreadPriority, Uint},
};
use core::ptr::NonNull;
use delegate::delegate;

// Define the OS adapter types
os_adapter! {
    "sem" => OsSemaphore: blueos::sync::semaphore::Semaphore,
}

impl OsSemaphore {
    delegate! {
        to self.inner() {
            pub fn init(&self, counter: Uint);
            pub fn count(&self) -> blueos::types::Uint;
            pub fn try_acquire<M: InsertModeTrait>(&self) -> bool;
            pub fn acquire_notimeout<M: InsertModeTrait>(&self) -> bool;
            pub fn acquire_timeout<M: InsertModeTrait>(&self, t: Tick) -> bool;
            pub fn acquire<M: InsertModeTrait>(&self, timeout: Tick) -> bool;
            pub fn release(&self);
        }
    }
}

#[cfg(event_flags)]
os_adapter! {
    "evt" => OsEventFlags: blueos::sync::event_flags::EventFlags,
}

#[cfg(event_flags)]
impl OsEventFlags {
    delegate! {
        to self.inner() {
            pub fn init(&self, flags: u32);
            pub fn get(&self) -> u32;
            pub fn set(&self, flags: u32) -> Result<u32, Error>;
            pub fn clear(&self, flags: u32) -> u32;
            pub fn wait<M: InsertModeTrait>(&self, flags: u32, mode: EventFlagsMode, timeout: Tick) -> Result<u32, Error>;
        }
    }
}

os_adapter! {
    "mqueue" => OsMessageQueue: blueos::sync::mqueue::MessageQueue,
}

impl OsMessageQueue {
    delegate! {
        to self.inner() {
            pub fn node_info(&self) -> (usize, u32);
            pub fn sendable_count(&self) -> u32;
            pub fn recvable_count(&self) ->u32;
            pub fn send(&self, buffer: &[u8], size: usize, timeout: Tick, urgent: SendMode) -> Result<(), Error>;
            pub fn recv(&self, buffer: &mut [u8], size: usize, timeout: Tick) -> Result<(), Error>;
            pub fn reset(&self);
        }
    }
}

os_adapter! {
    "mutex" => OsMutex: blueos::sync::mutex::Mutex,
}

impl OsMutex {
    delegate! {
        to self.inner() {
            pub fn pend_for(&self, timeout: Tick) -> bool;
            pub fn post(&self);
            pub fn owner(&self) -> Option<thread::ThreadNode>;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::thread::{Builder, Entry};
    use blueos_test_macro::test;

    use alloc::boxed::Box;

    os_adapter! {
        "th" => TestThread: blueos::thread::Thread {
            test_field1: u32,
            test_field2: u32,
        }
    }

    /// Helper function to create a name array from a string
    fn create_name_array(name: &str) -> [u8; MAX_NAME_LEN] {
        let mut name_array = [0u8; MAX_NAME_LEN];
        let bytes = name.as_bytes();
        let len = core::cmp::min(bytes.len(), MAX_NAME_LEN - 1);
        name_array[..len].copy_from_slice(&bytes[..len]);
        name_array
    }

    extern "C" fn test_thread_entry() {
        // do nothing
    }

    #[test]
    fn test_os_thread_creation() {
        let thread = Builder::new(Entry::C(test_thread_entry)).build();
        let name = create_name_array("thread0");
        let os_thread = TestThread::new(thread.clone(), name, 1, 2);
        assert_eq!(os_thread.name(), "thread0");
        // 1 in global queue, 1 in os_thread, 1 in ready queue
        // total 3, drop one reference here
        drop(os_thread);
        scheduler::queue_ready_thread(thread::IDLE, thread);
        scheduler::yield_me(); // to retire the thread
    }

    #[test]
    fn test_os_thread_creation2() {
        let thread = Builder::new(Entry::C(test_thread_entry)).build();
        let os_thread = TestThread::with_default_name(thread.clone());
        assert_eq!(os_thread.name(), "th1");
        // 1 in global queue, 1 in os_thread, 1 in ready queue
        // total 3, drop one reference here
        drop(os_thread);
        scheduler::queue_ready_thread(thread::IDLE, thread);
        scheduler::yield_me(); // to retire the thread
    }
}
