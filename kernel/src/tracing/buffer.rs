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
use spin::Mutex;

pub const RECORD_CAPACITY: usize = 512;

#[derive(Clone, Copy)]
pub struct RingBuffer {
    pub records: [EventRecord; RECORD_CAPACITY],
    pub write_idx: usize,
    pub len: usize,
    pub dropped: usize,
}

impl RingBuffer {
    pub const fn new() -> Self {
        Self {
            records: [EventRecord::empty(); RECORD_CAPACITY],
            write_idx: 0,
            len: 0,
            dropped: 0,
        }
    }
}

static RING: Mutex<RingBuffer> = Mutex::new(RingBuffer::new());

pub fn init() {
    let mut w = RING.lock();
    // Avoid constructing a large RingBuffer temporary on the stack.
    // For 32-bit targets this structure is ~18KB and can overflow early
    // boot stacks (e.g. 8KB on qemu_mps2_an385).
    w.write_idx = 0;
    w.len = 0;
    w.dropped = 0;
}

// Returns true if an old record was overwritten.
pub fn push(record: EventRecord) -> bool {
    let mut w = RING.lock();
    let mut overwritten = false;
    if w.len == RECORD_CAPACITY {
        w.dropped = w.dropped.saturating_add(1);
        overwritten = true;
    } else {
        w.len += 1;
    }
    let idx = w.write_idx;
    w.records[idx] = record;
    w.write_idx = (idx + 1) % RECORD_CAPACITY;
    overwritten
}

pub fn with_ring<R>(f: impl FnOnce(&RingBuffer) -> R) -> R {
    let w = RING.lock();
    f(&w)
}
