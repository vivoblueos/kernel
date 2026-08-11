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

use super::event::EventRecord;
use core::{
    cell::UnsafeCell,
    cmp,
    sync::atomic::{AtomicUsize, Ordering},
};

pub const RECORD_CAPACITY: usize = 512;
const NUM_CPUS: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;
const INVALID_SEQ: usize = usize::MAX;

struct Slot {
    record: UnsafeCell<EventRecord>,
    commit_seq: AtomicUsize,
}

impl Slot {
    const fn new() -> Self {
        Self {
            record: UnsafeCell::new(EventRecord::empty()),
            commit_seq: AtomicUsize::new(INVALID_SEQ),
        }
    }
}

// SAFETY: Slot concurrent access is coordinated by commit sequence atomics.
unsafe impl Sync for Slot {}

struct CpuRing {
    write_seq: AtomicUsize,
    slots: [Slot; RECORD_CAPACITY],
}

impl CpuRing {
    const fn new() -> Self {
        Self {
            write_seq: AtomicUsize::new(0),
            slots: [const { Slot::new() }; RECORD_CAPACITY],
        }
    }

    fn init(&self) {
        self.write_seq.store(0, Ordering::Relaxed);
        for slot in &self.slots {
            slot.commit_seq.store(INVALID_SEQ, Ordering::Relaxed);
        }
    }
}

static RINGS: [CpuRing; NUM_CPUS] = [const { CpuRing::new() }; NUM_CPUS];

pub fn init() {
    for ring in &RINGS {
        ring.init();
    }
}

// Returns true if an old record was overwritten.
pub fn push(record: EventRecord) -> bool {
    let cpu_id = crate::arch::current_cpu_id();
    let ring = &RINGS[cpu_id];

    // Reserve a slot lock-free. This is safe under IRQ and SMP because each
    // writer gets a unique sequence number.
    let seq = ring.write_seq.fetch_add(1, Ordering::Relaxed);
    let idx = seq % RECORD_CAPACITY;
    let slot = &ring.slots[idx];
    // SAFETY: this slot is uniquely owned by `seq` until commit_seq is set.
    unsafe { *slot.record.get() = record };
    // Publish the record after write is complete.
    slot.commit_seq.store(seq, Ordering::Release);

    seq >= RECORD_CAPACITY
}

pub fn for_each_committed(mut f: impl FnMut(EventRecord) -> bool) {
    for ring in &RINGS {
        // Snapshot writer progress for this CPU ring.
        let end_seq = ring.write_seq.load(Ordering::Acquire);
        let span = cmp::min(end_seq, RECORD_CAPACITY);
        let start_seq = end_seq - span;
        for seq in start_seq..end_seq {
            let idx = seq % RECORD_CAPACITY;
            let slot = &ring.slots[idx];
            // A slot belongs to this sequence only when commit_seq matches.
            if slot.commit_seq.load(Ordering::Acquire) != seq {
                continue;
            }
            // SAFETY: commit_seq == seq guarantees a fully published record.
            let record = unsafe { *slot.record.get() };
            if !f(record) {
                return;
            }
        }
    }
}
