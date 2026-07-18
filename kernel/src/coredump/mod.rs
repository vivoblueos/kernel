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

//! BlueKernel coredump module.
//!
//! Generates an ELF ET_CORE file on-device, covering registers and memory.
//! Supports multiple backends (file, logging, memory) and dump modes.

pub mod arch;
pub mod backend;
pub mod elf;
pub mod notes;
pub mod regions;
pub mod signal;

use crate::coredump::arch::capture_current_regs;
use crate::coredump::backend::{CoredumpBackend, COREDUMP_BUF_SIZE};
use crate::coredump::elf::{build_elf, CoredumpReason};
use crate::coredump::notes::build_notes;
use crate::coredump::regions::{collect_regions, DumpMode};
use core::sync::atomic::{AtomicBool, Ordering};
use core::fmt::Write;

/// Recursion guard: prevents re-entrant coredumps.
static COREDUMP_IN_PROGRESS: AtomicBool = AtomicBool::new(false);

/// Static buffer for building the ELF coredump.
///
/// Must be large enough to hold the ELF header, program headers, notes,
/// and all segment data (BSS, stacks). On 64-bit platforms where BSS can
/// be 2+ MB and system stacks 512 KB, 4 MB is required. On 32-bit
/// platforms 256 KB suffices.
///
/// Using a static buffer instead of a stack allocation avoids stack
/// overflow since thread stacks (64 KB) are much smaller than the
/// coredump buffer.
#[link_section = ".coredump_bss"]
static mut ELF_BUF: [u8; COREDUMP_BUF_SIZE] = [0u8; COREDUMP_BUF_SIZE];

/// Maximum combined size of all notes (must match notes.rs).
const NOTES_BUF_SIZE: usize = 2048;

/// Static buffer for formatting the coredump file path at runtime.
/// Used by FileBackend when VFS is enabled.
#[cfg(all(enable_vfs, not(coredump_mem_backend)))]
static mut COREDUMP_PATH_BUF: [u8; 64] = [0u8; 64];

/// Helper: writes a formatted path into a `&mut [u8]` buffer.
#[cfg(all(enable_vfs, not(coredump_mem_backend)))]
#[derive(Debug)]
struct PathWriter {
    buf: &'static mut [u8],
    pos: usize,
}

#[cfg(all(enable_vfs, not(coredump_mem_backend)))]
impl Write for PathWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let remaining = self.buf.len().saturating_sub(self.pos);
        let n = core::cmp::min(s.len(), remaining);
        self.buf[self.pos..self.pos + n].copy_from_slice(s.as_bytes());
        self.pos += n;
        Ok(())
    }
}

/// Generate a coredump with the given reason and dump mode.
///
/// Returns `true` if the coredump was successfully generated.
///
/// # Safety
///
/// Must be called with interrupts disabled. The coredump buffer is
/// a large stack allocation — ensure the stack is large enough.
#[inline(never)]
pub fn dump(reason: &CoredumpReason, mode: DumpMode) -> bool {
    // Recursion guard
    if COREDUMP_IN_PROGRESS.swap(true, Ordering::AcqRel) {
        return false;
    }

    // Static buffer for the ELF output.
    // SAFETY: coredump runs with interrupts disabled and COREDUMP_IN_PROGRESS
    // prevents re-entry, so exclusive access is guaranteed.
    let elf_buf = unsafe { &mut *core::ptr::addr_of_mut!(ELF_BUF) };

    // ── Step 1: Capture registers ──────────────────────────────────────
    let regs = capture_current_regs();

    // ── Step 2: Build notes ────────────────────────────────────────────
    let tid = crate::scheduler::current_thread_id();
    let (notes_buf, notes_written) = build_notes(tid, &regs, reason);

    // ── Step 3: Collect memory regions ─────────────────────────────────
    let collector = collect_regions(mode);
    let segments = collector.segments();

    // ── Step 4: Build ELF ──────────────────────────────────────────────
    let notes_slice = &notes_buf[..notes_written];
    match build_elf(notes_slice, segments, &mut elf_buf[..]) {
        Ok(written) => {
            // ── Step 5: Output via backend ─────────────────────────────
            // Backend selection priority: MemoryBackend > FileBackend > LoggingBackend
            #[cfg(coredump_mem_backend)]
            let mut backend = {
                // SAFETY: COREDUMP_STORAGE is a static mut buffer; coredump runs
                // with interrupts disabled and COREDUMP_IN_PROGRESS guard prevents
                // re-entry, so exclusive write access is guaranteed.
                let buf = unsafe { &mut COREDUMP_STORAGE[..] };
                backend::MemoryBackend::new(buf)
            };
            #[cfg(all(not(coredump_mem_backend), enable_vfs))]
            let mut backend = {
                let pid = crate::scheduler::current_thread_id();
                let path: &'static str = unsafe {
                    let mut writer = PathWriter { buf: &mut COREDUMP_PATH_BUF, pos: 0 };
                    let _ = write!(writer, "/tmp/blueos.core.{}", pid);
                    let len = writer.pos;
                    core::str::from_utf8_unchecked(&COREDUMP_PATH_BUF[..len])
                };
                backend::FileBackend::new(path)
            };
            #[cfg(all(not(coredump_mem_backend), not(enable_vfs), not(cortex_m)))]
            let mut backend = backend::LoggingBackend::new();
            #[cfg(all(not(coredump_mem_backend), not(enable_vfs), cortex_m))]
            let mut backend = backend::LoggingBackend::new();

            backend.write(&elf_buf[..written]);
            backend.finalize(mode);

            COREDUMP_IN_PROGRESS.store(false, Ordering::Release);
            true
        }
        Err(()) => {
            // Buffer too small — log and abort
            #[cfg(not(use_defmt))]
            semihosting::eprintln!("[COREDUMP] ELF buffer exhausted ({})", COREDUMP_BUF_SIZE);
            #[cfg(use_defmt)]
            defmt::error!("[COREDUMP] ELF buffer exhausted");
            COREDUMP_IN_PROGRESS.store(false, Ordering::Release);
            false
        }
    }
}

/// Generate a coredump using the default backend for the current platform.
///
/// Convenience wrapper that calls `dump()` with `DumpMode::Current`.
pub fn dump_current(reason: &CoredumpReason) -> bool {
    dump(reason, DumpMode::Current)
}

/// Reserved coredump buffer for the MemoryBackend (256 KB).
#[cfg(coredump_mem_backend)]
#[link_section = ".coredump_bss"]
pub static mut COREDUMP_STORAGE: [u8; COREDUMP_BUF_SIZE] = [0u8; COREDUMP_BUF_SIZE];

/// Valid flag for MemoryBackend: set to `true` after a coredump is written.
#[cfg(coredump_mem_backend)]
pub(crate) static COREDUMP_VALID: AtomicBool = AtomicBool::new(false);

/// Initialize the coredump subsystem.
///
/// When the MemoryBackend is enabled, clears the storage buffer and
/// resets the valid flag so a fresh coredump can be detected.
#[cfg(coredump_mem_backend)]
pub fn init() {
    // SAFETY: called once at boot, single-threaded, before any coredump.
    unsafe {
        core::ptr::write_bytes(COREDUMP_STORAGE.as_mut_ptr(), 0, COREDUMP_BUF_SIZE);
    }
    COREDUMP_VALID.store(false, Ordering::Release);
}

/// Initialize the coredump subsystem (no-op when MemoryBackend is disabled).
#[cfg(not(coredump_mem_backend))]
pub fn init() {}
