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

//! Coredump backends.
//!
//! Backends receive the finished ELF coredump buffer for output.
//! Two built-in backends:
//!   - `FileBackend`: writes via the VFS (QEMU/GDB scenarios)
//!   - `LoggingBackend`: hex-encodes and prints (serial/log scenarios)
//!   - `MemoryBackend`: stores in a static buffer (for post-mortem retrieval)

use crate::coredump::DumpMode;
use crate::vfs::FileOps;

/// Maximum coredump buffer size.
///
/// Controlled by Kconfig `CONFIG_COREDUMP_BUF_SIZE` (int, in bytes).
/// Falls back to an arch-appropriate default if Kconfig is absent.
/// 64-bit → 4 MB, 32-bit (non-Cortex-M) → 256 KB, Cortex-M → 64 KB.
#[cfg(enable_coredump)]
pub const COREDUMP_BUF_SIZE: usize =
    blueos_kconfig::CONFIG_COREDUMP_BUF_SIZE as usize;
#[cfg(not(enable_coredump))]
pub const COREDUMP_BUF_SIZE: usize = 4096;

/// Backend trait for coredump output.
pub trait CoredumpBackend {
    /// Write a chunk of the finished coredump.
    fn write(&mut self, buf: &[u8]);

    /// Signal that the coredump is complete.
    fn finalize(&mut self, mode: DumpMode);

    /// Return a descriptive name for this backend.
    fn name(&self) -> &str;
}

// ── FileBackend ─────────────────────────────────────────────────────────

/// Writes the coredump to a file via VFS.
///
/// Used in QEMU/GDB scenarios where a filesystem is available.
/// The file path is typically `/tmp/blueos.core.<pid>`.
#[derive(Debug)]
pub struct FileBackend {
    path: &'static str,
    written: usize,
}

impl FileBackend {
    pub const fn new(path: &'static str) -> Self {
        Self { path, written: 0 }
    }
}

impl CoredumpBackend for FileBackend {
    fn write(&mut self, buf: &[u8]) {
        #[cfg(enable_vfs)]
        {
            // Append to the coredump file via VFS.
            if let Ok(file) = crate::vfs::path::open_path(self.path, libc::O_WRONLY | libc::O_CREAT | libc::O_APPEND, 0o666) {
                let _ = file.write(buf);
            }
        }
        #[cfg(not(enable_vfs))]
        {
            let _ = buf;
        }
        self.written += buf.len();
    }

    fn finalize(&mut self, _mode: DumpMode) {
        // File is already flushed on each write; nothing extra needed.
    }

    fn name(&self) -> &str {
        "file"
    }
}

// ── LoggingBackend ──────────────────────────────────────────────────────

/// Hex-encodes the coredump and outputs via the kernel logger.
///
/// Used in embedded/no-GDB scenarios where only a serial/console
/// output channel is available. The host can reassemble the hex stream.
#[derive(Debug)]
pub struct LoggingBackend {
    chunks: usize,
}

impl LoggingBackend {
    pub const fn new() -> Self {
        Self { chunks: 0 }
    }
}

/// Hex-encode a byte slice into the given buffer (2× input size).
fn hex_encode(src: &[u8], dst: &mut [u8]) -> usize {
    let n = core::cmp::min(src.len(), dst.len() / 2);
    for (i, &b) in src[..n].iter().enumerate() {
        dst[i * 2] = hex_nib(b >> 4);
        dst[i * 2 + 1] = hex_nib(b & 0x0f);
    }
    n * 2
}

#[inline]
fn hex_nib(v: u8) -> u8 {
    if v < 10 {
        b'0' + v
    } else {
        b'a' + v - 10
    }
}

impl CoredumpBackend for LoggingBackend {
    fn write(&mut self, buf: &[u8]) {
        // Output in small hex-encoded lines via console
        const LINE_MAX: usize = 64; // 32 bytes per line → 64 hex chars
        let mut hex_buf = [0u8; LINE_MAX * 2 + 1]; // +1 for newline
        for chunk in buf.chunks(LINE_MAX) {
            let n = hex_encode(chunk, &mut hex_buf);
            hex_buf[n] = b'\n';
            // Use semihosting eprint which is always available
            let s = unsafe { core::str::from_utf8_unchecked(&hex_buf[..n + 1]) };
            semihosting::eprint!("{}", s);
        }
        self.chunks += 1;
    }

    fn finalize(&mut self, mode: DumpMode) {
        // Emit a trailer line with metadata
        let size_kb = self.chunks * 32 / 1024;
        semihosting::eprint!(
            "[BLUEOS_COREDUMP_END] mode={:?} chunks={} size={}KB\n",
            mode,
            self.chunks,
            size_kb,
        );
    }

    fn name(&self) -> &str {
        "logging"
    }
}

// ── MemoryBackend ───────────────────────────────────────────────────────

/// Stores the coredump in a fixed static buffer.
///
/// Used for post-mortem retrieval by a subsequent boot or
/// by a debugger attached after the fact.
#[derive(Debug)]
pub struct MemoryBackend {
    buf: &'static mut [u8],
    pos: usize,
}

impl MemoryBackend {
    pub fn new(buf: &'static mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }
}

impl CoredumpBackend for MemoryBackend {
    fn write(&mut self, data: &[u8]) {
        let remaining = self.buf.len().saturating_sub(self.pos);
        let n = core::cmp::min(data.len(), remaining);
        self.buf[self.pos..self.pos + n].copy_from_slice(&data[..n]);
        self.pos += n;
    }

    fn finalize(&mut self, _mode: DumpMode) {
        #[cfg(coredump_mem_backend)]
        crate::coredump::COREDUMP_VALID.store(true, core::sync::atomic::Ordering::Release);
    }

    fn name(&self) -> &str {
        "memory"
    }
}
