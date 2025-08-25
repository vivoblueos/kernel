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
use crate::{
    arch, debug,
    error::{code, Error},
    scheduler, static_arc, support,
    sync::SpinLock,
    thread,
    thread::{Thread, ThreadNode},
    time::WAITING_FOREVER,
    trace,
    types::{
        impl_simple_intrusive_adapter, Arc, ArcList, ArcListIterator, AtomicIlistHead as ListHead,
        StaticListOwner, UniqueListHead,
    },
};
use core::sync::atomic::{AtomicUsize, Ordering};
use scheduler::WaitQueue;
use support::PerCpu;

impl_simple_intrusive_adapter!(Sync, AtomicWaitEntry, sync_node);

type Head = ListHead<AtomicWaitEntry, Sync>;
type EntryNode = Arc<AtomicWaitEntry>;
type EntryListHead = UniqueListHead<AtomicWaitEntry, Sync, SyncEntry>;

#[derive(Default, Debug)]
pub struct SyncEntry;

impl const StaticListOwner<AtomicWaitEntry, Sync> for SyncEntry {
    fn get() -> &'static Arc<SpinLock<Head>> {
        &SYNC_ENTRIES
    }
}

#[derive(Debug)]
pub struct AtomicWaitEntry {
    sync_node: EntryListHead,
    addr: usize,
    pending: SpinLock<WaitQueue>,
}

impl AtomicWaitEntry {
    pub fn init(&self) -> bool {
        return self.pending.irqsave_lock().init();
    }

    pub fn addr(&self) -> usize {
        self.addr
    }

    pub fn new(addr: usize) -> Self {
        Self {
            sync_node: EntryListHead::new(),
            addr,
            pending: SpinLock::new(WaitQueue::new()),
        }
    }
}

static_arc! {
    SYNC_ENTRIES(SpinLock<Head>, SpinLock::new(Head::new())),
}

pub fn atomic_wait(atom: &AtomicUsize, val: usize, timeout: Option<usize>) -> Result<(), Error> {
    let current_val = atom.load(Ordering::Acquire);
    if current_val != val {
        return Err(code::EAGAIN);
    }
    // We should not wait in IRQ.
    let mut w = EntryListHead::lock();
    // Make the second check.
    let current_val = atom.load(Ordering::Acquire);
    if current_val != val {
        return Err(code::EAGAIN);
    }
    let mut entry = None;
    let addr = atom as *const _ as usize;
    for e in ArcListIterator::new(w.get_list_mut(), None) {
        if e.addr() == addr {
            entry = Some(e);
            break;
        }
    }
    let entry = entry.map_or_else(
        || {
            let entry = Arc::new(AtomicWaitEntry::new(addr));
            entry.init();
            w.insert(entry.clone());
            entry
        },
        |e| e,
    );
    let t = scheduler::current_thread();
    let mut we = entry.pending.irqsave_lock();
    we.take_irq_guard(w.get_guard_mut());
    drop(w);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] will be waiting @ 0x{:x}",
        scheduler::current_thread_id(),
        addr
    );
    if let Some(timeout) = timeout {
        let res = scheduler::suspend_me_with_timeout(we, timeout);
        if res {
            return Err(code::ETIMEDOUT);
        }
    } else {
        let _ = scheduler::suspend_me_with_timeout(we, WAITING_FOREVER);
    }
    Ok(())
}

pub fn atomic_wake(atom: &AtomicUsize, how_many: usize) -> Result<usize, Error> {
    if how_many == 0 {
        return Ok(0);
    }
    let addr = atom as *const _ as usize;
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] Waking up @ 0x{:x}",
        scheduler::current_thread_id(),
        addr
    );
    let mut woken = 0;
    let mut w = EntryListHead::lock();
    for e in ArcListIterator::new(w.get_list_mut(), None) {
        if e.addr() != addr {
            continue;
        }
        let mut we = e.pending.irqsave_lock();
        while let Some(next) = we.pop_front() {
            if scheduler::queue_ready_thread(thread::SUSPENDED, next.thread.clone()) {
                woken += 1;
                #[cfg(debugging_scheduler)]
                crate::trace!(
                    "[TH:0x{:x}] Woken up 0x{:x}",
                    scheduler::current_thread_id(),
                    Thread::id(&next.thread)
                );
            }
            if woken == how_many {
                break;
            }
        }
        if we.is_empty() {
            w.detach(&mut e.clone());
        }
        if woken == how_many {
            break;
        }
    }
    drop(w);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] woken up {} threads",
        scheduler::current_thread_id(),
        woken
    );
    scheduler::yield_me_now_or_later();
    Ok(woken)
}

#[cfg(cortex_m)]
#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};

    static ATOM: AtomicUsize = AtomicUsize::new(0);

    #[test]
    fn test_atomic_wait_timeout() {
        let result = atomic_wait(&ATOM, 0, Some(10));
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), code::ETIMEDOUT);
        atomic_wake(&ATOM, 1);
    }
}
