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

use super::{buffer, control};

#[repr(C)]
struct TraceFileHeader {
    magic: [u8; 4],
    version: u16,
    header_size: u16,
    flags: u32,
    boot_time_ns: u64,
    tsc_freq_hz: u64,
    cpu_count: u32,
    reserved: u32,
}

impl TraceFileHeader {
    const fn new() -> Self {
        Self {
            magic: *b"BTRC",
            version: 1,
            header_size: core::mem::size_of::<TraceFileHeader>() as u16,
            flags: 0,
            boot_time_ns: 0,
            tsc_freq_hz: 0,
            cpu_count: blueos_kconfig::CONFIG_NUM_CORES as u32,
            reserved: 0,
        }
    }
}

#[inline]
fn put_u8(out: &mut [u8], off: &mut usize, v: u8) -> bool {
    if *off + 1 > out.len() {
        return false;
    }
    out[*off] = v;
    *off += 1;
    true
}

#[inline]
fn put_u16(out: &mut [u8], off: &mut usize, v: u16) -> bool {
    if *off + 2 > out.len() {
        return false;
    }
    out[*off..*off + 2].copy_from_slice(&v.to_le_bytes());
    *off += 2;
    true
}

#[inline]
fn put_u32(out: &mut [u8], off: &mut usize, v: u32) -> bool {
    if *off + 4 > out.len() {
        return false;
    }
    out[*off..*off + 4].copy_from_slice(&v.to_le_bytes());
    *off += 4;
    true
}

#[inline]
fn put_u64(out: &mut [u8], off: &mut usize, v: u64) -> bool {
    if *off + 8 > out.len() {
        return false;
    }
    out[*off..*off + 8].copy_from_slice(&v.to_le_bytes());
    *off += 8;
    true
}

fn write_header(out: &mut [u8], off: &mut usize) -> bool {
    let hdr = TraceFileHeader::new();
    if *off + core::mem::size_of::<TraceFileHeader>() > out.len() {
        return false;
    }
    out[*off..*off + 4].copy_from_slice(&hdr.magic);
    *off += 4;
    put_u16(out, off, hdr.version)
        && put_u16(out, off, hdr.header_size)
        && put_u32(out, off, hdr.flags)
        && put_u64(out, off, hdr.boot_time_ns)
        && put_u64(out, off, hdr.tsc_freq_hz)
        && put_u32(out, off, hdr.cpu_count)
        && put_u32(out, off, hdr.reserved)
}

pub fn dump_to_slice(out: &mut [u8]) -> usize {
    let mut off = 0;
    if !write_header(out, &mut off) {
        return 0;
    }

    // Emit a synthetic dropped counter event into dump metadata region.
    let stats = control::stats();
    if !put_u64(out, &mut off, stats.dropped_events as u64) {
        return off;
    }

    buffer::for_each_committed(|rec| {
        if !(put_u64(out, &mut off, rec.header.ts_ns)
            && put_u16(out, &mut off, rec.header.event_id)
            && put_u16(out, &mut off, rec.header.cpu_id)
            && put_u32(out, &mut off, rec.header.tid)
            && put_u8(out, &mut off, rec.header.phase)
            && put_u8(out, &mut off, rec.header.flags)
            && put_u16(out, &mut off, rec.header.payload_len))
        {
            return false;
        }
        for datum in rec.data {
            if !put_u64(out, &mut off, datum as u64) {
                return false;
            }
        }
        true
    });
    off
}
