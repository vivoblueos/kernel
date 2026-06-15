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

#![no_std]

use core::sync::atomic::{AtomicPtr, Ordering};
use log::{LevelFilter, Metadata, Record};

/// Callbacks that the logger needs from the kernel environment.
/// These are set once during `logger_init` and never changed.
pub struct LoggerHooks {
    /// Returns the current timestamp in milliseconds since boot.
    pub timestamp_ms: fn() -> u128,
    /// Returns the current CPU/core ID.
    pub cpu_id: fn() -> usize,
    /// Returns the current thread ID.
    pub thread_id: fn() -> usize,
    /// Writes a formatted log line to the output.
    pub write: fn(line: &str),
}

static HOOKS: AtomicPtr<LoggerHooks> = AtomicPtr::new(core::ptr::null_mut());

#[cfg(log_level_off)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Off;
#[cfg(log_level_error)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Error;
#[cfg(log_level_warn)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Warn;
#[cfg(log_level_info)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Info;
#[cfg(log_level_debug)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Debug;
#[cfg(log_level_trace)]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Trace;

struct Logger;

/// Initialize the logger. Must be called once at boot time.
/// `hooks` must be a `&'static LoggerHooks` (or leaked Box).
pub fn logger_init(hooks: &'static LoggerHooks) {
    HOOKS.store(
        hooks as *const LoggerHooks as *mut LoggerHooks,
        Ordering::Release,
    );
    static LOGGER: Logger = Logger {};
    log::set_max_level(DEFAULT_LOG_LEVEL);
    log::set_logger(&LOGGER).unwrap();
}

impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let hooks = HOOKS.load(Ordering::Acquire);
        if hooks.is_null() {
            return;
        }
        let hooks = unsafe { &*hooks };
        let timestamp = (hooks.timestamp_ms)();
        let cpu = (hooks.cpu_id)();
        let tid = (hooks.thread_id)();

        // Use a fixed-size buffer to avoid alloc
        let mut buf: [u8; 256] = [0; 256];
        use core::fmt::Write;
        let mut w = FixedBufWriter {
            buf: &mut buf,
            pos: 0,
        };
        let _ = core::write!(
            &mut w,
            "[T:{:09} C:{} TH:0x{:x}][{}] {}\n",
            timestamp,
            cpu,
            tid,
            record.level(),
            record.args()
        );
        let len = w.pos;
        if len > 0 {
            // Convert to &str and call the write hook
            let s = unsafe { core::str::from_utf8_unchecked(&w.buf[..len]) };
            (hooks.write)(s);
        }
    }

    fn flush(&self) {}
}

/// A simple fixed-buffer writer for `core::fmt::Write`.
struct FixedBufWriter<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> core::fmt::Write for FixedBufWriter<'a> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let bytes = s.as_bytes();
        let remaining = self.buf.len() - self.pos;
        let to_write = bytes.len().min(remaining);
        self.buf[self.pos..self.pos + to_write].copy_from_slice(&bytes[..to_write]);
        self.pos += to_write;
        Ok(())
    }
}
