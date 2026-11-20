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
    support::DisableInterruptGuard,
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
fn inner_next_thread(tbl: &mut ReadyTable, index: usize) -> Option<ThreadNode> {
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
    let irq = DisableInterruptGuard::new();
    next_preferred_thread_with(prio, mode, &irq)
}
#[inline(always)]
pub(crate) fn next_preferred_thread_with(
    prio: ThreadPriority,
    mode: PreferMode,
    irq: &DisableInterruptGuard,
) -> Option<ThreadNode> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().lock_with(irq) };
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
    inner_next_thread(&mut tbl, highest_active as usize)
}

pub fn next_ready_thread() -> Option<ThreadNode> {
    let irq = DisableInterruptGuard::new();
    next_ready_thread_with(&irq)
}
#[inline(always)]
pub(crate) fn next_ready_thread_with(irq: &DisableInterruptGuard) -> Option<ThreadNode> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().lock_with(irq) };
    let highest_active = tbl.highest_active();

    #[cfg(debugging_scheduler)]
    {
        use crate::arch;
        crate::trace!("next_ready_thread highest_active {}", highest_active);
    }
    if highest_active > MAX_THREAD_PRIORITY as u32 {
        return None;
    }
    inner_next_thread(&mut tbl, highest_active as usize)
}

// Peek at the highest ready priority without popping. Used by
// yield_me_now_or_later to skip pendsv when no higher-priority thread is
// runnable — pendsv round-trips are not free and critical-section exits call
// this at high frequency.
#[inline]
pub fn highest_ready_priority() -> Option<ThreadPriority> {
    let tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    let highest_active = tbl.highest_active();
    if highest_active > MAX_THREAD_PRIORITY as u32 {
        return None;
    }
    Some(highest_active as ThreadPriority)
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
fn queue_ready_thread_inner(tbl: &mut ReadyTable, t: &ThreadNode) -> bool {
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
    let irq = DisableInterruptGuard::new();
    queue_ready_thread_with(old_state, &t, &irq)
}
#[inline(always)]
pub(crate) fn queue_ready_thread_with(
    old_state: Uint,
    t: &ThreadNode,
    irq: &DisableInterruptGuard,
) -> Result<(), Uint> {
    if old_state == thread::READY {
        return Err(thread::READY);
    }
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().lock_with(irq) };
    t.transfer_state(old_state, thread::READY)?;
    let ok = queue_ready_thread_inner(&mut tbl, t);
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
            Thread::id(t),
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

fn remove_from_ready_queue_inner(
    tbl: &mut ReadyTable,
    t: &ThreadNode,
    old_priority: ThreadPriority,
) -> bool {
    debug_assert!(old_priority <= MAX_THREAD_PRIORITY);
    let q = &mut tbl.tables[old_priority as usize];
    // Conservatively search the whole queue.
    let removed = q.remove_if(|e| core::ptr::eq(ThreadNode::as_ptr(t), e));
    let Some(removed) = removed else {
        return false;
    };
    if q.is_empty() {
        tbl.clear_active_queue(old_priority as u32);
    }
    true
}

pub fn remove_from_ready_queue(t: &ThreadNode) -> bool {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    remove_from_ready_queue_inner(&mut tbl, t, t.priority())
}

pub fn update_ready_thread_priority(
    t: &ThreadNode,
    new_priority: ThreadPriority,
) -> Result<(), Uint> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if !remove_from_ready_queue_inner(&mut tbl, t, t.priority()) {
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

// Like update_ready_thread_priority, but the caller passes the thread's
// priority as it was *before* any promote_priority_to mutation, so we can
// locate the thread in the correct ready queue even if priority was already
// bumped. Use this from priority-inheritance paths that change t.priority()
// before re-queuing.
pub fn update_ready_thread_priority_from(
    t: &ThreadNode,
    old_priority: ThreadPriority,
    new_priority: ThreadPriority,
) -> Result<(), Uint> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if !remove_from_ready_queue_inner(&mut tbl, t, old_priority) {
        let state = t.state();
        // Thread is not in the ready queue. Set the priority field anyway so
        // the next enqueue uses the correct bucket. Known cases:
        //   RUNNING  — normal: another core scheduled it (SMP), or is current
        //   READY    — benign: next_ready_thread already popped it; the caller
        //              already ran recover_priority, but we do it here too.
        //   SUSPENDED/RETIRED — thread is blocked or dying; field-only update.
        let mut thread_guard = t.lock();
        thread_guard.set_priority(new_priority);
        drop(thread_guard);
        return Err(state);
    }
    t.lock().set_priority(new_priority);
    if queue_ready_thread_inner(&mut tbl, t) {
        return Ok(());
    }
    Err(thread::RUNNING)
}

/// Atomically set `t`'s priority: re-queue it if it is in the ready queue,
/// otherwise still write the field — but do so *inside* the ReadyTable irqsave
/// critical section so the "not in queue" decision and the field write cannot
/// be separated by an IRQ-driven SUSPENDED→READY (which would strand the
/// thread in the old priority bucket). Use this from priority-set entry
/// points (osThreadSetPriority); PI paths keep using
/// `update_ready_thread_priority`.
pub fn set_thread_priority(t: &ThreadNode, new_priority: ThreadPriority) -> Result<(), Uint> {
    let mut tbl = unsafe { READY_TABLE.assume_init_ref().irqsave_lock() };
    if remove_from_ready_queue_inner(&mut tbl, t, t.priority()) {
        let mut thread_guard = t.lock();
        thread_guard.set_priority(new_priority);
        drop(thread_guard);
        if queue_ready_thread_inner(&mut tbl, t) {
            return Ok(());
        }
        return Err(thread::RUNNING);
    }
    // Not in the ready queue (RUNNING or SUSPENDED): set the field while still
    // holding the ReadyTable irqsave lock to close the TOCTOU window.
    let state = t.state();
    let mut thread_guard = t.lock();
    thread_guard.set_priority(new_priority);
    drop(thread_guard);
    drop(tbl);
    Err(state)
}
