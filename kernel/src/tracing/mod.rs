// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

pub mod buffer;
pub mod control;
pub mod dump;
pub mod event;

pub use control::{TraceConfig, TraceStats};
use event::{EventId, EventPhase, EventRecord, RecordHeader};

#[inline]
fn now_ns() -> u64 {
    crate::time::now().as_nanos() as u64
}

#[inline]
fn current_tid() -> u32 {
    if crate::scheduler::is_schedule_ready() {
        crate::scheduler::current_thread_id() as u32
    } else {
        0
    }
}

#[inline]
fn record_raw(event_id: EventId, phase: EventPhase, tid: u32, data: [usize; 4]) {
    if !control::should_record(event_id) {
        return;
    }
    let record = EventRecord {
        header: RecordHeader {
            ts_ns: now_ns(),
            event_id: event_id as u16,
            cpu_id: crate::arch::current_cpu_id() as u16,
            tid,
            phase: phase as u8,
            flags: 0,
            payload_len: core::mem::size_of::<[usize; 4]>() as u16,
        },
        data,
    };
    let overwritten = buffer::push(record);
    control::on_event_recorded();
    if overwritten {
        control::on_event_dropped(1);
    }
}

pub fn init() {
    control::init();
    buffer::init();
}

pub fn start(cfg: TraceConfig) -> bool {
    control::configure(cfg);
    let started = control::start();
    if started {
        record_raw(
            EventId::TraceStart,
            EventPhase::Instant,
            0,
            [cfg.event_mask, cfg.sample_rate, cfg.buffer_kb, 0],
        );
    }
    started
}

pub fn stop(reason: u16) -> bool {
    if !control::enabled() {
        return false;
    }
    record_raw(
        EventId::TraceStop,
        EventPhase::Instant,
        0,
        [reason as usize, 0, 0, 0],
    );
    control::stop()
}

#[inline]
pub fn enabled() -> bool {
    control::enabled()
}

#[inline]
pub fn stats() -> TraceStats {
    control::stats()
}

#[inline]
pub fn dump_to_slice(out: &mut [u8]) -> usize {
    dump::dump_to_slice(out)
}

#[inline]
pub fn record_sched_switch(
    prev_tid: u32,
    next_tid: u32,
    prev_prio: usize,
    next_prio: usize,
    prev_state: usize,
) {
    record_raw(
        EventId::SchedSwitch,
        EventPhase::Instant,
        next_tid,
        [prev_tid as usize, next_tid as usize, prev_prio, (next_prio << 16) | prev_state],
    );
}

#[inline]
pub fn record_thread_create(new_tid: u32, parent_tid: u32, prio: usize, kind: usize) {
    record_raw(
        EventId::ThreadCreate,
        EventPhase::Instant,
        current_tid(),
        [new_tid as usize, parent_tid as usize, prio, kind],
    );
}

#[inline]
pub fn record_thread_exit(tid: u32, code: isize) {
    record_raw(
        EventId::ThreadExit,
        EventPhase::Instant,
        tid,
        [tid as usize, code as usize, 0, 0],
    );
}

#[inline]
pub fn record_thread_wakeup(target_tid: u32, by_tid: u32, reason: usize, obj_id: usize) {
    record_raw(
        EventId::ThreadWakeup,
        EventPhase::Instant,
        by_tid,
        [target_tid as usize, by_tid as usize, reason, obj_id],
    );
}

#[inline]
pub fn record_thread_block(tid: u32, reason: usize, obj_id: usize, timeout: usize) {
    record_raw(
        EventId::ThreadBlock,
        EventPhase::Instant,
        tid,
        [tid as usize, reason, obj_id, timeout],
    );
}

#[inline]
pub fn record_irq_enter(irq: u16, kind: u8, nesting: u8) {
    record_raw(
        EventId::IrqEnter,
        EventPhase::Begin,
        0,
        [irq as usize, kind as usize, nesting as usize, 0],
    );
}

#[inline]
pub fn record_irq_exit(irq: u16, kind: u8, nesting: u8) {
    record_raw(
        EventId::IrqExit,
        EventPhase::End,
        0,
        [irq as usize, kind as usize, nesting as usize, 0],
    );
}

#[inline]
pub fn record_sys_enter(nr: usize, arg0: usize, arg1: usize, arg2: usize) {
    record_raw(
        EventId::SysEnter,
        EventPhase::Begin,
        current_tid(),
        [nr, arg0, arg1, arg2],
    );
}

#[inline]
pub fn record_sys_exit(nr: usize, ret: isize, errno: isize) {
    record_raw(
        EventId::SysExit,
        EventPhase::End,
        current_tid(),
        [nr, ret as usize, errno as usize, 0],
    );
}

#[inline]
pub fn record_lock_wait_begin(lock_id: usize, lock_type: usize) {
    record_raw(
        EventId::LockWaitBegin,
        EventPhase::Begin,
        current_tid(),
        [lock_id, lock_type, 0, 0],
    );
}

#[inline]
pub fn record_lock_wait_end(lock_id: usize, success: bool) {
    record_raw(
        EventId::LockWaitEnd,
        EventPhase::End,
        current_tid(),
        [lock_id, success as usize, 0, 0],
    );
}

#[inline]
pub fn record_lock_hold_begin(lock_id: usize, owner_tid: u32) {
    record_raw(
        EventId::LockHoldBegin,
        EventPhase::Begin,
        owner_tid,
        [lock_id, owner_tid as usize, 0, 0],
    );
}

#[inline]
pub fn record_lock_hold_end(lock_id: usize) {
    record_raw(
        EventId::LockHoldEnd,
        EventPhase::End,
        current_tid(),
        [lock_id, 0, 0, 0],
    );
}

#[inline]
pub fn record_mm_alloc(ptr: usize, size: usize, align: usize, heap_id: usize) {
    record_raw(
        EventId::MmAlloc,
        EventPhase::Instant,
        current_tid(),
        [ptr, size, align, heap_id],
    );
}

#[inline]
pub fn record_mm_free(ptr: usize, size: usize, heap_id: usize) {
    record_raw(
        EventId::MmFree,
        EventPhase::Instant,
        current_tid(),
        [ptr, size, heap_id, 0],
    );
}

#[inline]
pub fn record_mm_alloc_fail(size: usize, align: usize, heap_id: usize) {
    record_raw(
        EventId::MmAllocFail,
        EventPhase::Instant,
        current_tid(),
        [size, align, heap_id, 0],
    );
}
