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
    arch,
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
    debug_assert!(ReadyTableBitFields::BITS >= ThreadPriority::BITS);
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
    let next = q.pop_front()?;
    debug_assert_eq!(next.state(), thread::READY);
    if q.is_empty() {
        tbl.clear_active_queue(index as u32);
    }
    Some(next)
}

// Mode for selecting the next preferred thread.
#[derive(Clone, Copy, Debug)]
pub enum PreferMode {
    /// Only pick a thread with strictly higher priority.
    StrictHigher,
    /// Pick a thread with the same or higher priority.
    SameOrHigher,
}

#[inline(always)]
pub fn next_preferred_thread(prio: ThreadPriority, mode: PreferMode) -> Option<ThreadNode> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    let highest_active = tbl.highest_active();
    // highest_active is trailing_zeros(): 0 = highest priority. When a
    // same-priority ready thread exists, highest_active == prio.
    match mode {
        PreferMode::StrictHigher => {
            if highest_active >= prio as u32 {
                return None;
            }
        }
        PreferMode::SameOrHigher => {
            if highest_active > prio as u32 {
                return None;
            }
        }
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
    if old_state == thread::READY {
        return None;
    }
    if t.transfer_state(old_state, thread::READY).is_err() {
        return None;
    }
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if !queue_ready_thread_inner(&mut tbl, &t) {
        // back to old_state.
        t.transfer_state(thread::READY, old_state);
        return None;
    }
    drop(tbl);
    Some(post_action())
}

#[inline]
fn queue_ready_thread_inner(tbl: &mut SpinLockGuard<'_, ReadyTable>, t: &ThreadNode) -> bool {
    let priority = t.priority();
    debug_assert!(priority <= MAX_THREAD_PRIORITY);
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
pub fn queue_ready_thread(old_state: Uint, t: ThreadNode) -> Result<(), Uint> {
    if old_state == thread::READY {
        return Err(thread::READY);
    }
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    t.transfer_state(old_state, thread::READY)?;
    let ok = queue_ready_thread_inner(&mut tbl, &t);
    if !ok {
        // push_back failed: thread is in READY state with sched_node still
        // detached. Roll back to old_state so the thread stays in its wait
        // queue. If this rollback CAS also fails, the thread has been
        // concurrently mutated by another path and is now stranded in READY
        // with no ready-queue linkage — a permanent ghost that no scheduler
        // path can recover. Surface it loudly.
        let rollback = t.transfer_state(thread::READY, old_state);
        debug_assert!(
            rollback.is_ok(),
            "queue_ready_thread rollback failed for TH:0x{:x}: state was {:?}, expected READY; alien_ptr={:?}, priority={}, thread is now ghost",
            Thread::id(&t),
            rollback,
            t.get_alien_ptr(),
            t.priority(),
        );
        return Err(old_state);
    }
    drop(tbl);
    #[cfg(smp)]
    super::notify_idle_cores(1);
    Ok(())
}

fn remove_from_ready_queue_inner(tbl: &mut SpinLockGuard<'_, ReadyTable>, t: &ThreadNode) -> bool {
    let priority = t.priority();
    debug_assert!(priority <= MAX_THREAD_PRIORITY);
    let q = &mut tbl.tables[priority as usize];
    // Conservatively search the whole queue.
    let removed = q.remove_if(|e| core::ptr::eq(ThreadNode::as_ptr(t), e));
    let Some(removed) = removed else {
        return false;
    };
    if q.is_empty() {
        tbl.clear_active_queue(priority as u32);
    }
    true
}

pub fn remove_from_ready_queue(t: &ThreadNode) -> bool {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    remove_from_ready_queue_inner(&mut tbl, t)
}

pub fn update_ready_thread_priority(
    t: &ThreadNode,
    new_priority: ThreadPriority,
) -> Result<(), Uint> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if !remove_from_ready_queue_inner(&mut tbl, t) {
        let state = t.state();
        return Err(state);
    }

    let mut thread_guard = t.lock();
    thread_guard.set_priority(new_priority);
    drop(thread_guard);

    if queue_ready_thread_inner(&mut tbl, t) {
        return Ok(());
    }
    Err(thread::RUNNING)
}
