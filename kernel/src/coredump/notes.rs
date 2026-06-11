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

//! NT_PRSTATUS, NT_PRPSINFO, NT_SIGINFO note builders.
//!
//! Uses a fixed-size staging buffer — no heap, no alloc.

use crate::coredump::elf::*;
use core::mem;

/// Maximum combined size of all notes.
const NOTES_BUF_SIZE: usize = 2048;

/// Write cursor over a `&mut [u8]`.
struct NoteCursor<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> NoteCursor<'a> {
    fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    fn remaining(&self) -> usize {
        self.buf.len().saturating_sub(self.pos)
    }

    fn push(&mut self, data: &[u8]) {
        let end = self.pos + data.len();
        if end <= self.buf.len() {
            self.buf[self.pos..end].copy_from_slice(data);
            self.pos = end;
        }
    }

    fn pad4(&mut self) {
        let pad = (4 - (self.pos & 3)) & 3;
        if pad > 0 {
            self.push(&[0u8; 3][..pad]);
        }
    }

    fn written(&self) -> &[u8] {
        &self.buf[..self.pos]
    }
}

/// Append a single ELF note (Nhdr + name + desc, 4-byte aligned) into `cursor`.
fn push_note(cur: &mut NoteCursor, n_type: u32, name: &[u8], desc: &[u8]) {
    let nhdr = Nhdr {
        n_namesz: name.len() as u32,
        n_descsz: desc.len() as u32,
        n_type,
    };
    let nhdr_bytes = unsafe {
        core::slice::from_raw_parts(&nhdr as *const Nhdr as *const u8, mem::size_of::<Nhdr>())
    };
    cur.push(nhdr_bytes);
    cur.push(name);
    cur.pad4();
    cur.push(desc);
    cur.pad4();
}

/// Build all notes (NT_PRSTATUS + NT_PRPSINFO + NT_SIGINFO) into `notes_buf`.
///
/// Returns the buffer and the actual number of bytes written.
pub fn build_notes(tid: usize, regs: &[u8], reason: &CoredumpReason) -> ([u8; NOTES_BUF_SIZE], usize) {
    let mut buf = [0u8; NOTES_BUF_SIZE];
    let mut cur = NoteCursor::new(&mut buf);

    // ── NT_PRSTATUS ─────────────────────────────────────────────────
    // Layout: siginfo-like header + pid/ppid/pgrp/sid + registers
    let prstatus_desc = build_prstatus_descriptor(tid, regs, reason);
    push_note(&mut cur, NT_PRSTATUS, b"CORE", &prstatus_desc);

    // ── NT_PRPSINFO ─────────────────────────────────────────────────
    struct Prpsinfo {
        state: u8,
        sname: i8,
        zombie: u8,
        nice: u8,
        _pad: [u8; 4],
        uid: u16,
        gid: u16,
        pid: u32,
        ppid: u32,
        pgrp: u32,
        sid: u32,
        fname: [u8; 16],
        psargs: [u8; 80],
    }
    let mut fname = [0u8; 16];
    fname[..7].copy_from_slice(b"blueos\x00");
    let prpsinfo = Prpsinfo {
        state: 0,
        sname: b'?' as i8,
        zombie: 0,
        nice: 0,
        _pad: [0u8; 4],
        uid: 0,
        gid: 0,
        pid: tid as u32,
        ppid: 0,
        pgrp: 0,
        sid: 0,
        fname,
        psargs: [0u8; 80],
    };
    let prpsinfo_bytes = unsafe {
        core::slice::from_raw_parts(
            &prpsinfo as *const Prpsinfo as *const u8,
            mem::size_of::<Prpsinfo>(),
        )
    };
    push_note(&mut cur, NT_PRPSINFO, b"CORE", prpsinfo_bytes);

    // ── NT_SIGINFO ──────────────────────────────────────────────────
    let reason_bytes = unsafe {
        core::slice::from_raw_parts(
            reason as *const CoredumpReason as *const u8,
            mem::size_of::<CoredumpReason>(),
        )
    };
    push_note(&mut cur, NT_SIGINFO, b"CORE", reason_bytes);

    // Record the actual written length, zero the rest
    let written = cur.pos;
    if written < NOTES_BUF_SIZE {
        buf[written..].fill(0);
    }
    (buf, written)
}

/// Return the maximum notes buffer size.
/// The actual written length is returned alongside the buffer by `build_notes`.
pub fn notes_len() -> usize {
    NOTES_BUF_SIZE
}

/// Build NT_PRSTATUS descriptor: siginfo (12/16 bytes) + pad + pid/ppid/pgrp/sid + regs.
fn build_prstatus_descriptor(tid: usize, regs: &[u8], reason: &CoredumpReason) -> [u8; 1100] {
    let mut desc = [0u8; 1100];
    let mut pos = 0usize;

    // si_signo (4 bytes)
    desc[pos..pos + 4].copy_from_slice(&reason.signo.to_ne_bytes());
    pos += 4;
    // si_code (4 bytes)
    desc[pos..pos + 4].copy_from_slice(&reason.code.to_ne_bytes());
    pos += 4;
    // si_errno (4 bytes)
    let zero32: [u8; 4] = 0u32.to_ne_bytes();
    desc[pos..pos + 4].copy_from_slice(&zero32);
    pos += 4;

    // padding: 2 × pointer-sized int
    let pad_sz = 2 * mem::size_of::<usize>();
    pos += pad_sz;

    // pid
    desc[pos..pos + 4].copy_from_slice(&(tid as u32).to_ne_bytes());
    pos += 4;
    // ppid
    desc[pos..pos + 4].copy_from_slice(&zero32);
    pos += 4;
    // pgrp
    desc[pos..pos + 4].copy_from_slice(&zero32);
    pos += 4;
    // sid
    desc[pos..pos + 4].copy_from_slice(&zero32);
    pos += 4;

    // registers
    let regs_len = core::cmp::min(regs.len(), desc.len().saturating_sub(pos));
    desc[pos..pos + regs_len].copy_from_slice(&regs[..regs_len]);

    desc
}
