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

use super::{ProcDir, ProcFileOps};
use crate::{
    error::{code, Error},
    vfs::inode_mode::InodeMode,
};
use alloc::{string::String, vec, vec::Vec};
use core::{fmt::Write, str};

const TRACE_HEADER_LEN: usize = 36;
const DROPPED_META_LEN: usize = 8;
const RECORDS_OFFSET: usize = TRACE_HEADER_LEN + DROPPED_META_LEN;
const RECORD_SERIALIZED_LEN: usize = 52;

pub(super) fn init_trace_files(root: &ProcDir) -> Result<(), Error> {
    let trace_dir = root.create_dir("trace", true)?;
    trace_dir.create_proc_file("control", TraceControl, InodeMode::from(0o644), true)?;
    trace_dir.create_proc_file("stats", TraceStats, InodeMode::from(0o444), true)?;
    trace_dir.create_proc_file("dump", TraceDump, InodeMode::from(0o444), true)?;
    trace_dir.create_proc_file("raw", TraceRaw, InodeMode::from(0o444), true)?;
    Ok(())
}

struct TraceControl;
struct TraceStats;
struct TraceDump;
struct TraceRaw;

impl ProcFileOps for TraceControl {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        #[cfg(tracing)]
        {
            let enabled = crate::tracing::enabled();
            let mut out = String::new();
            writeln!(&mut out, "compiled_in=1").ok();
            writeln!(&mut out, "enabled={}", enabled as u8).ok();
            writeln!(&mut out, "commands=start stop reset").ok();
            return Ok(out.into_bytes());
        }
        #[cfg(not(tracing))]
        {
            Ok(b"tracing is disabled in this build\n".to_vec())
        }
    }

    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error> {
        let cmd = str::from_utf8(&content)
            .map_err(|_| code::EINVAL)?
            .trim()
            .to_ascii_lowercase();
        if cmd.is_empty() {
            return Err(code::EINVAL);
        }

        #[cfg(tracing)]
        {
            match cmd.as_str() {
                "start" => {
                    if !crate::tracing::start(crate::tracing::TraceConfig::default()) {
                        return Err(code::EBUSY);
                    }
                }
                "stop" => {
                    if !crate::tracing::stop(0) {
                        return Err(code::EINVAL);
                    }
                }
                "reset" => crate::tracing::reset(),
                _ => return Err(code::EINVAL),
            }
            Ok(content.len())
        }
        #[cfg(not(tracing))]
        {
            Err(code::ENOTSUP)
        }
    }
}

impl ProcFileOps for TraceStats {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        #[cfg(tracing)]
        {
            let stats = crate::tracing::stats();
            let mut out = String::new();
            writeln!(&mut out, "compiled_in=1").ok();
            writeln!(&mut out, "enabled={}", stats.enabled as u8).ok();
            writeln!(&mut out, "total_events={}", stats.total_events).ok();
            writeln!(&mut out, "dropped_events={}", stats.dropped_events).ok();
            return Ok(out.into_bytes());
        }
        #[cfg(not(tracing))]
        {
            Ok(
                b"compiled_in=0\nenabled=0\ntotal_events=0\ndropped_events=0\ntracing is disabled in this build\n"
                    .to_vec(),
            )
        }
    }

    fn set_content(&self, _content: Vec<u8>) -> Result<usize, Error> {
        Err(code::EPERM)
    }
}

impl ProcFileOps for TraceDump {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        #[cfg(tracing)]
        {
            let raw = dump_raw_bytes()?;
            decode_dump(&raw)
        }
        #[cfg(not(tracing))]
        {
            Ok(b"tracing is disabled in this build\n".to_vec())
        }
    }

    fn set_content(&self, _content: Vec<u8>) -> Result<usize, Error> {
        Err(code::EPERM)
    }
}

impl ProcFileOps for TraceRaw {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        #[cfg(tracing)]
        {
            dump_raw_bytes()
        }
        #[cfg(not(tracing))]
        {
            Ok(b"tracing is disabled in this build\n".to_vec())
        }
    }

    fn set_content(&self, _content: Vec<u8>) -> Result<usize, Error> {
        Err(code::EPERM)
    }
}

#[cfg(tracing)]
fn dump_raw_bytes() -> Result<Vec<u8>, Error> {
    let max_records =
        crate::tracing::buffer::RECORD_CAPACITY * blueos_kconfig::CONFIG_NUM_CORES as usize;
    let mut raw = vec![0u8; RECORDS_OFFSET + max_records * RECORD_SERIALIZED_LEN];
    let written = crate::tracing::dump_to_slice(&mut raw);
    raw.truncate(written);
    Ok(raw)
}

#[cfg(tracing)]
fn decode_dump(raw: &[u8]) -> Result<Vec<u8>, Error> {
    if raw.len() < RECORDS_OFFSET {
        return Ok(b"trace dump is empty\n".to_vec());
    }
    if raw[0..4] != *b"BTRC" {
        return Err(code::EINVAL);
    }

    let dropped = read_u64(raw, TRACE_HEADER_LEN).ok_or(code::EINVAL)?;
    let mut out = String::new();
    writeln!(&mut out, "format=BTRC v1 dropped_events={}", dropped).ok();
    writeln!(
        &mut out,
        "ts_ns,event,event_id,cpu,tid,phase,data0,data1,data2,data3"
    )
    .ok();

    let mut off = RECORDS_OFFSET;
    let mut count = 0usize;
    while off + RECORD_SERIALIZED_LEN <= raw.len() {
        let ts_ns = read_u64(raw, off).ok_or(code::EINVAL)?;
        let event_id = read_u16(raw, off + 8).ok_or(code::EINVAL)?;
        let cpu_id = read_u16(raw, off + 10).ok_or(code::EINVAL)?;
        let tid = read_u32(raw, off + 12).ok_or(code::EINVAL)?;
        let phase = raw[off + 16];
        let d0 = read_u64(raw, off + 20).ok_or(code::EINVAL)?;
        let d1 = read_u64(raw, off + 28).ok_or(code::EINVAL)?;
        let d2 = read_u64(raw, off + 36).ok_or(code::EINVAL)?;
        let d3 = read_u64(raw, off + 44).ok_or(code::EINVAL)?;
        writeln!(
            &mut out,
            "{},{},0x{:04x},{},{},{},{},{},{},{}",
            ts_ns,
            event_name(event_id),
            event_id,
            cpu_id,
            tid,
            phase_name(phase),
            d0,
            d1,
            d2,
            d3
        )
        .ok();
        off += RECORD_SERIALIZED_LEN;
        count += 1;
    }
    if count == 0 {
        writeln!(&mut out, "(no events)").ok();
    }
    Ok(out.into_bytes())
}

#[cfg(tracing)]
fn event_name(event_id: u16) -> &'static str {
    use crate::tracing::event::EventId;
    match event_id {
        x if x == EventId::TraceStart as u16 => "TraceStart",
        x if x == EventId::TraceStop as u16 => "TraceStop",
        x if x == EventId::TraceDropped as u16 => "TraceDropped",
        x if x == EventId::SchedSwitch as u16 => "SchedSwitch",
        x if x == EventId::ThreadCreate as u16 => "ThreadCreate",
        x if x == EventId::ThreadExit as u16 => "ThreadExit",
        x if x == EventId::ThreadWakeup as u16 => "ThreadWakeup",
        x if x == EventId::ThreadBlock as u16 => "ThreadBlock",
        x if x == EventId::IrqEnter as u16 => "IrqEnter",
        x if x == EventId::IrqExit as u16 => "IrqExit",
        x if x == EventId::SysEnter as u16 => "SysEnter",
        x if x == EventId::SysExit as u16 => "SysExit",
        x if x == EventId::LockWaitBegin as u16 => "LockWaitBegin",
        x if x == EventId::LockWaitEnd as u16 => "LockWaitEnd",
        x if x == EventId::LockHoldBegin as u16 => "LockHoldBegin",
        x if x == EventId::LockHoldEnd as u16 => "LockHoldEnd",
        x if x == EventId::MmAlloc as u16 => "MmAlloc",
        x if x == EventId::MmFree as u16 => "MmFree",
        x if x == EventId::MmAllocFail as u16 => "MmAllocFail",
        x if x == EventId::CounterMemUsedBytes as u16 => "CounterMemUsedBytes",
        _ => "Unknown",
    }
}

#[cfg(tracing)]
fn phase_name(phase: u8) -> &'static str {
    match phase {
        1 => "B",
        2 => "E",
        3 => "I",
        4 => "C",
        _ => "?",
    }
}

#[cfg(tracing)]
#[inline]
fn read_u16(buf: &[u8], off: usize) -> Option<u16> {
    if off + 2 > buf.len() {
        return None;
    }
    Some(u16::from_le_bytes([buf[off], buf[off + 1]]))
}

#[cfg(tracing)]
#[inline]
fn read_u32(buf: &[u8], off: usize) -> Option<u32> {
    if off + 4 > buf.len() {
        return None;
    }
    Some(u32::from_le_bytes([
        buf[off],
        buf[off + 1],
        buf[off + 2],
        buf[off + 3],
    ]))
}

#[cfg(tracing)]
#[inline]
fn read_u64(buf: &[u8], off: usize) -> Option<u64> {
    if off + 8 > buf.len() {
        return None;
    }
    Some(u64::from_le_bytes([
        buf[off],
        buf[off + 1],
        buf[off + 2],
        buf[off + 3],
        buf[off + 4],
        buf[off + 5],
        buf[off + 6],
        buf[off + 7],
    ]))
}
