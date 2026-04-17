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

#![cfg(tracing)]

use blueos::{
    allocator,
    tracing::{self, event::EventId, TraceConfig},
};
use blueos_test_macro::test;
use semihosting::println;

const TRACE_HEADER_LEN: usize = 36;
const DROPPED_META_LEN: usize = 8;
const RECORDS_OFFSET: usize = TRACE_HEADER_LEN + DROPPED_META_LEN;
const RECORD_SERIALIZED_LEN: usize = 52;

#[inline]
fn event_id_at(buf: &[u8], event_offset: usize) -> u16 {
    let event_id_offset = event_offset + 8;
    u16::from_le_bytes([buf[event_id_offset], buf[event_id_offset + 1]])
}

fn collect_event_ids(buf: &[u8], len: usize) -> alloc::vec::Vec<u16> {
    let mut ids = alloc::vec::Vec::new();
    let mut off = RECORDS_OFFSET;
    while off + RECORD_SERIALIZED_LEN <= len {
        ids.push(event_id_at(buf, off));
        off += RECORD_SERIALIZED_LEN;
    }
    ids
}

fn has_event(ids: &[u16], event: EventId) -> bool {
    ids.iter().any(|id| *id == event as u16)
}

fn event_name(event_id: u16) -> &'static str {
    if event_id == EventId::TraceStart as u16 {
        "TraceStart"
    } else if event_id == EventId::TraceStop as u16 {
        "TraceStop"
    } else if event_id == EventId::TraceDropped as u16 {
        "TraceDropped"
    } else if event_id == EventId::SchedSwitch as u16 {
        "SchedSwitch"
    } else if event_id == EventId::ThreadCreate as u16 {
        "ThreadCreate"
    } else if event_id == EventId::ThreadExit as u16 {
        "ThreadExit"
    } else if event_id == EventId::ThreadWakeup as u16 {
        "ThreadWakeup"
    } else if event_id == EventId::ThreadBlock as u16 {
        "ThreadBlock"
    } else if event_id == EventId::IrqEnter as u16 {
        "IrqEnter"
    } else if event_id == EventId::IrqExit as u16 {
        "IrqExit"
    } else if event_id == EventId::SysEnter as u16 {
        "SysEnter"
    } else if event_id == EventId::SysExit as u16 {
        "SysExit"
    } else if event_id == EventId::LockWaitBegin as u16 {
        "LockWaitBegin"
    } else if event_id == EventId::LockWaitEnd as u16 {
        "LockWaitEnd"
    } else if event_id == EventId::LockHoldBegin as u16 {
        "LockHoldBegin"
    } else if event_id == EventId::LockHoldEnd as u16 {
        "LockHoldEnd"
    } else if event_id == EventId::MmAlloc as u16 {
        "MmAlloc"
    } else if event_id == EventId::MmFree as u16 {
        "MmFree"
    } else if event_id == EventId::MmAllocFail as u16 {
        "MmAllocFail"
    } else if event_id == EventId::CounterMemUsedBytes as u16 {
        "CounterMemUsedBytes"
    } else {
        "Unknown"
    }
}

fn print_events(ids: &[u16]) {
    println!("[tracing-test] dumped {} event(s):", ids.len());
    for (idx, id) in ids.iter().enumerate() {
        println!(
            "[tracing-test]   #{:02} {} (0x{:04x})",
            idx,
            event_name(*id),
            id
        );
    }
}

#[test]
fn test_tracing_records_real_system_events() {
    // Keep test deterministic across runs.
    if tracing::enabled() {
        let _ = tracing::stop(0);
    }
    tracing::init();

    let initial = tracing::stats();
    assert_eq!(initial.total_events, 0);
    assert_eq!(initial.dropped_events, 0);
    assert!(!initial.enabled);

    assert!(tracing::start(TraceConfig::default()));
    assert!(tracing::enabled());
    assert!(!tracing::start(TraceConfig::default()));

    // Trigger memory alloc/free events from the real allocator path.
    let p = allocator::malloc(128);
    assert!(!p.is_null());
    allocator::free(p);

    let running = tracing::stats();
    assert!(running.enabled);
    assert!(
        running.total_events >= 3,
        "expected at least TraceStart + 2 probe events, got {}",
        running.total_events
    );

    let mut dump = [0u8; 4096];
    let dumped = tracing::dump_to_slice(&mut dump);
    assert!(dumped > RECORDS_OFFSET, "dump is too small: {}", dumped);
    assert_eq!(&dump[0..4], b"BTRC");

    let event_ids = collect_event_ids(&dump, dumped);
    assert!(!event_ids.is_empty(), "no events found in dump");
    print_events(&event_ids);
    assert!(
        has_event(&event_ids, EventId::TraceStart),
        "TraceStart not found in dump"
    );
    assert!(
        has_event(&event_ids, EventId::MmAlloc),
        "MmAlloc not found in dump"
    );
    assert!(
        has_event(&event_ids, EventId::MmFree),
        "MmFree not found in dump"
    );

    let before_stop_total = running.total_events;
    assert!(tracing::stop(0));
    assert!(!tracing::enabled());
    let stopped = tracing::stats();
    assert!(!stopped.enabled);
    assert!(
        stopped.total_events >= before_stop_total + 1,
        "TraceStop should be recorded when stopping"
    );

    let stable_total = stopped.total_events;
    let p2 = allocator::malloc(64);
    assert!(!p2.is_null());
    allocator::free(p2);
    let after_stop_probe = tracing::stats();
    assert_eq!(after_stop_probe.total_events, stable_total);
}
