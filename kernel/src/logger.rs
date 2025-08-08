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

use crate::{
    arch, kprintln, scheduler, sync::SpinLock, thread::Thread, time::tick_get_millisecond,
};
use log::{LevelFilter, Metadata, Record};

static LOGGER_MUTEX: SpinLock<()> = SpinLock::new(());

struct Logger;

pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

///set max log level
pub fn set_max_level(level: LogLevel) {
    match level {
        LogLevel::Trace => log::set_max_level(LevelFilter::Trace),
        LogLevel::Debug => log::set_max_level(LevelFilter::Debug),
        LogLevel::Info => log::set_max_level(LevelFilter::Info),
        LogLevel::Warn => log::set_max_level(LevelFilter::Warn),
        LogLevel::Error => log::set_max_level(LevelFilter::Error),
    }
}

/// log init
pub fn logger_init() {
    static LOGGER: Logger = Logger {};
    #[cfg(debug)]
    log::set_max_level(LevelFilter::Trace);
    #[cfg(release)]
    log::set_max_level(LevelFilter::Warn);
    log::set_logger(&LOGGER).unwrap();
}

///impl log for Logger
impl log::Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= log::max_level()
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }
        let timestamp = tick_get_millisecond();
        let tid = scheduler::current_thread_id();
        let cpu = arch::current_cpu_id();
        let _guard = LOGGER_MUTEX.irqsave_lock();
        kprintln!(
            "[T:{:09} C:{} TH:0x{:x}][{}] {} ",
            timestamp,
            cpu,
            tid,
            record.level(),
            record.args()
        );
    }

    fn flush(&self) {}
}
