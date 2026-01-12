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

pub mod timer;
pub mod timer_manager;

use crate::{arch, scheduler, support::DisableInterruptGuard};
use blueos_kconfig::CONFIG_TICKS_PER_SECOND as TICKS_PER_SECOND;
use core::time::Duration;
// ClockImpl should be provided by each board.
pub use crate::boards::ClockImpl;
use crate::devices::clock::Clock;

#[derive(Default, Debug, PartialEq, Clone, Copy, Eq, PartialOrd, Ord)]
pub struct Tick(pub usize);

impl Tick {
    pub const MAX: Self = Self(usize::MAX);

    pub fn from_millis(millis: u64) -> Self {
        Self((millis * (TICKS_PER_SECOND as u64) / 1000) as usize)
    }

    pub fn from_micros(micros: u64) -> Self {
        Self((micros * (TICKS_PER_SECOND as u64) / 1_000_000) as usize)
    }

    pub fn from_nanos(nanos: u64) -> Self {
        Self((nanos * (TICKS_PER_SECOND as u64) / 1_000_000_000) as usize)
    }

    pub fn after(n: Self) -> Self {
        if n == Self::MAX {
            return Self::MAX;
        }
        let now = Self::now();
        Self(Self::now().0 + n.0)
    }

    pub fn add(&self, n: Self) -> Self {
        if *self == Self::MAX {
            return Self::MAX;
        }
        Self(self.0 + n.0)
    }

    pub fn since(&self, base: Self) -> Self {
        if self.0 <= base.0 {
            return Self(0);
        }
        Tick(self.0 - base.0)
    }

    pub fn now() -> Self {
        debug_assert_eq!(ClockImpl::hz() % TICKS_PER_SECOND as u64, 0);
        Self(
            (ClockImpl::estimate_current_cycles() * TICKS_PER_SECOND as u64 / ClockImpl::hz())
                as usize,
        )
    }

    pub fn interrupt_after(diff: Self) {
        let nth = Self::after(diff);
        Self::interrupt_at(nth);
    }

    pub fn interrupt_at(n: Tick) {
        let _guard = DisableInterruptGuard::new();
        if n == Self::MAX {
            ClockImpl::stop();
            return;
        }
        ClockImpl::interrupt_at(ClockImpl::hz() * n.0 as u64 / TICKS_PER_SECOND as u64);
    }
}

pub(crate) extern "C" fn handle_clock_interrupt() {
    let _guard = DisableInterruptGuard::new();
    let now = Tick::now();
    if let Some(next_deadline) = timer::expire_timers(now) {
        Tick::interrupt_at(next_deadline);
    } else {
        ClockImpl::stop();
    };
    if !scheduler::need_reschedule_at(now) {
        return;
    }
    scheduler::yield_me_now_or_later();
}

pub fn current_clock_cycles() -> u64 {
    ClockImpl::estimate_current_cycles()
}

pub fn now() -> Duration {
    from_clock_cycles(ClockImpl::estimate_current_cycles())
}

pub fn from_clock_cycles(cycles: u64) -> Duration {
    let now = 1_000_000_000 * cycles / ClockImpl::hz();
    Duration::from_nanos(now)
}

pub struct ScopeTimer<'a> {
    start: u64,
    diff: &'a mut u64,
}

impl<'a> ScopeTimer<'a> {
    pub fn new(diff: &'a mut u64) -> Self {
        Self {
            start: ClockImpl::estimate_current_cycles(),
            diff,
        }
    }
}

impl Drop for ScopeTimer<'_> {
    fn drop(&mut self) {
        *self.diff = ClockImpl::estimate_current_cycles() - self.start;
    }
}
