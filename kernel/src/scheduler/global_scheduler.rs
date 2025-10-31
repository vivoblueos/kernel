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
    sync::spinlock::{SpinLock, SpinLockGuard},
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

#[inline]
fn inner_next_thread(mut tbl: SpinLockGuard<'_, ReadyTable>, index: usize) -> Option<ThreadNode> {
    let q = &mut tbl.tables[index];
    let next = q.pop_front();
    assert!(next.is_some());
    if q.is_empty() {
        tbl.clear_active_queue(index as u32);
    }
    assert!(next.as_ref().unwrap().validate_saved_sp());
    next
}

pub fn next_preferred_thread(prio: ThreadPriority) -> Option<ThreadNode> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    let highest_active = tbl.highest_active();
    if highest_active > prio as u32 {
        return None;
    }
    inner_next_thread(tbl, highest_active as usize)
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
    inner_next_thread(tbl, highest_active as usize)
}

pub fn queue_ready_thread_with_post_action<R, F>(
    old_state: Uint,
    t: ThreadNode,
    post_action: F,
) -> Option<R>
where
    F: Fn() -> R,
{
    assert_ne!(old_state, thread::READY);
    if !t.transfer_state(old_state, thread::READY) {
        return None;
    }
    assert!(t.validate_saved_sp());
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if !queue_ready_thread_inner(&mut tbl, t) {
        return None;
    }
    Some(post_action())
}

#[inline]
fn queue_ready_thread_inner(tbl: &mut SpinLockGuard<'_, ReadyTable>, t: ThreadNode) -> bool {
    let priority = t.priority();
    assert!(priority <= MAX_THREAD_PRIORITY);
    let q = &mut tbl.tables[priority as usize];
    if !q.push_back(t.clone()) {
        return false;
    }
    tbl.set_active_queue(priority as u32);
    #[cfg(debugging_scheduler)]
    {
        use crate::arch;
        crate::trace!(
            "Current highest PRI {}, added PRI {}",
            tbl.highest_active(),
            priority,
        );
    }
    true
}

// We only queue the thread if old_state equals thread's current state.
pub fn queue_ready_thread(old_state: Uint, t: ThreadNode) -> bool {
    assert_ne!(old_state, thread::READY);
    if !t.transfer_state(old_state, thread::READY) {
        return false;
    }
    debug_assert!(t.validate_saved_sp());
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    queue_ready_thread_inner(&mut tbl, t)
}
