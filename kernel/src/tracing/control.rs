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

use super::event::EventId;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use spin::Mutex;

#[derive(Clone, Copy, Debug)]
pub struct TraceConfig {
    pub event_mask: usize,
    pub sample_rate: usize,
    pub buffer_kb: usize,
}

impl Default for TraceConfig {
    fn default() -> Self {
        Self {
            event_mask: usize::MAX,
            sample_rate: 1,
            #[cfg(tracing)]
            buffer_kb: blueos_kconfig::CONFIG_TRACING_BUFFER_KB as usize,
            #[cfg(not(tracing))]
            buffer_kb: 64,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct TraceStats {
    pub enabled: bool,
    pub total_events: usize,
    pub dropped_events: usize,
}

static ENABLED: AtomicBool = AtomicBool::new(false);
static TOTAL_EVENTS: AtomicUsize = AtomicUsize::new(0);
static DROPPED_EVENTS: AtomicUsize = AtomicUsize::new(0);
#[cfg(tracing)]
const DEFAULT_BUFFER_KB: usize = blueos_kconfig::CONFIG_TRACING_BUFFER_KB as usize;
#[cfg(not(tracing))]
const DEFAULT_BUFFER_KB: usize = 64;

static CONFIG: Mutex<TraceConfig> = Mutex::new(TraceConfig {
    event_mask: usize::MAX,
    sample_rate: 1,
    buffer_kb: DEFAULT_BUFFER_KB,
});

pub fn init() {
    ENABLED.store(false, Ordering::Relaxed);
    TOTAL_EVENTS.store(0, Ordering::Relaxed);
    DROPPED_EVENTS.store(0, Ordering::Relaxed);
}

pub fn configure(cfg: TraceConfig) {
    let mut w = CONFIG.lock();
    *w = cfg;
}

pub fn config() -> TraceConfig {
    *CONFIG.lock()
}

pub fn start() -> bool {
    !ENABLED.swap(true, Ordering::SeqCst)
}

pub fn stop() -> bool {
    ENABLED.swap(false, Ordering::SeqCst)
}

#[inline]
pub fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

#[inline]
pub fn should_record(_event_id: EventId) -> bool {
    enabled()
}

#[inline]
pub fn on_event_recorded() {
    TOTAL_EVENTS.fetch_add(1, Ordering::Relaxed);
}

#[inline]
pub fn on_event_dropped(dropped: usize) {
    DROPPED_EVENTS.fetch_add(dropped, Ordering::Relaxed);
}

pub fn stats() -> TraceStats {
    TraceStats {
        enabled: enabled(),
        total_events: TOTAL_EVENTS.load(Ordering::Relaxed),
        dropped_events: DROPPED_EVENTS.load(Ordering::Relaxed),
    }
}
