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

use log::{LevelFilter, Metadata, Record};

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
// Fallback for external crate compilation where cfg(log_level_*) isn't set
#[cfg(not(any(
    log_level_off, log_level_error, log_level_warn,
    log_level_info, log_level_debug, log_level_trace
)))]
const DEFAULT_LOG_LEVEL: LevelFilter = LevelFilter::Info;

/// Callback type for writing a log record to the output.
///
/// The callback receives the full log Record and is responsible for
/// formatting and outputting it (e.g. via `kprintln!`).
pub type LogWriter = fn(&Record);

struct Logger;

static mut LOG_WRITER: Option<LogWriter> = None;

/// Initialize the logger with a custom writer callback.
///
/// The writer is responsible for formatting and outputting each log record.
/// The kernel should provide a writer that uses `kprintln!` and accesses
/// its own `arch`, `scheduler`, and `time` modules to add timestamp, CPU,
/// and thread information.
pub fn logger_init(writer: LogWriter) {
    static LOGGER: Logger = Logger {};
    unsafe {
        LOG_WRITER = Some(writer);
    }
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
        if let Some(writer) = unsafe { LOG_WRITER } {
            writer(record);
        }
    }

    fn flush(&self) {}
}