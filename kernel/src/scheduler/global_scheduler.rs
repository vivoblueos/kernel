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

use crate::{
    config::MAX_THREAD_PRIORITY,
    sync::spinlock::SpinLock,
    thread,
    thread::{Thread, ThreadNode},
    types::{ArcList, ThreadPriority, Uint},
};
use core::mem::MaybeUninit;

static mut READY_TABLE: MaybeUninit<SpinLock<ReadyTable>> = MaybeUninit::zeroed();
type ReadyQueue = ArcList<Thread, thread::OffsetOfSchedNode>;
type ReadyTableBitFields = u32;

#[allow(clippy::assertions_on_constants)]
pub(super) fn init() {
    assert!(ReadyTableBitFields::BITS >= ThreadPriority::BITS);
    unsafe { READY_TABLE.write(SpinLock::new(ReadyTable::new())) };
    let mut w = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    for i in 0..(MAX_THREAD_PRIORITY + 1) as usize {
        w.tables[i].init();
    }
}

#[derive(Debug)]
struct ReadyTable {
    active_tables: ReadyTableBitFields,
    tables: [ReadyQueue; (MAX_THREAD_PRIORITY + 1) as usize],
}

impl ReadyTable {
    pub fn new() -> Self {
        Self {
            active_tables: 0,
            tables: [const { ReadyQueue::new() }; (MAX_THREAD_PRIORITY + 1) as usize],
        }
    }

    #[inline]
    fn clear_active_queue(&mut self, bit: u32) -> &mut Self {
        self.active_tables &= !(1 << bit);
        self
    }

    #[inline]
    fn set_active_queue(&mut self, bit: u32) -> &mut Self {
        self.active_tables |= 1 << bit;
        self
    }

    #[inline]
    fn highest_active(&self) -> u32 {
        self.active_tables.trailing_zeros()
    }
}

pub fn next_ready_thread() -> Option<ThreadNode> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    let highest_active = tbl.highest_active();

    #[cfg(debugging_scheduler)]
    {
        use crate::arch;
        crate::trace!("next_ready_thread highest_active {}", highest_active);
    }
    if highest_active > MAX_THREAD_PRIORITY as u32 {
        return None;
    }
    let q = &mut tbl.tables[highest_active as usize];
    let next = q.pop_front();
    assert!(next.is_some());
    if q.is_empty() {
        tbl.clear_active_queue(highest_active);
    }
    assert!(next.as_ref().unwrap().validate_saved_sp());
    next
}

// We only queue the thread if old_state equals thread's current state.
pub fn queue_ready_thread(old_state: Uint, t: ThreadNode) -> bool {
    assert!(old_state != thread::READY);
    if !t.transfer_state(old_state, thread::READY) {
        return false;
    }
    assert!(t.validate_saved_sp());
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    let priority = t.priority();
    assert!(priority <= MAX_THREAD_PRIORITY);
    let q = &mut tbl.tables[priority as usize];
    q.push_back(t.clone());
    tbl.set_active_queue(priority as u32);

    #[cfg(debugging_scheduler)]
    {
        use crate::arch;
        crate::trace!(
            "add pri {} get highest pri {}",
            priority,
            tbl.highest_active()
        );
    }
    true
}
