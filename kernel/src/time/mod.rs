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

pub mod systick;
pub mod timer;

use crate::{arch, boards, scheduler, support::DisableInterruptGuard, thread::Thread};
use blueos_kconfig::TICKS_PER_SECOND;
use systick::SYSTICK;

pub const NO_WAITING: usize = 0;
pub const WAITING_FOREVER: usize = usize::MAX;

pub fn systick_init(sys_clock: u32) -> bool {
    debug_assert!(sys_clock > 0);
    SYSTICK.init(sys_clock, TICKS_PER_SECOND as u32)
}

pub fn get_sys_cycles() -> u64 {
    SYSTICK.get_cycles()
}

pub fn cycles_to_millis(cycles: u64) -> u64 {
    (cycles as f32 * 1_000_000f32 / ((SYSTICK.get_step() * TICKS_PER_SECOND) as f32)) as u64
}

pub fn reset_systick() {
    SYSTICK.reset_counter();
}

pub extern "C" fn handle_tick_increment() {
    let _guard = DisableInterruptGuard::new();
    let mut need_schedule = false;
    // FIXME: aarch64 and riscv64 need to be supported
    if arch::current_cpu_id() == 0 {
        let ticks = SYSTICK.increment_ticks();
        need_schedule = timer::check_hard_timer(ticks);
    }
    need_schedule = need_schedule || scheduler::handle_tick_increment(1);
    SYSTICK.reset_counter();
    if need_schedule {
        scheduler::yield_me_now_or_later();
    }
}

pub fn tick_from_millisecond(ms: usize) -> usize {
    #[cfg(has_fpu)]
    {
        let ticks = TICKS_PER_SECOND * (ms / 1000);
        ticks + (TICKS_PER_SECOND * (ms % 1000) + 999) / 1000
    }
    // use 1024 as 1000 to aviod use math library
    #[cfg(not(has_fpu))]
    {
        let ticks = TICKS_PER_SECOND.wrapping_mul(ms >> 10);
        let remainder = ms & 0x3FF;
        ticks.wrapping_add((TICKS_PER_SECOND.wrapping_mul(remainder) + 1023) >> 10)
    }
}

pub fn tick_to_millisecond(ticks: usize) -> usize {
    ticks * (1000 / TICKS_PER_SECOND)
}

/// TickTime represents time in ticks.
///
/// Each tick corresponds to a system tick, which is defined by the system's tick rate (TICKS_PER_SECOND).
/// So the resolution of TickTime is 1 / TICKS_PER_SECOND seconds.
/// Use u64 to store ticks to avoid overflow in long running systems.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TickTime(u64);

impl TickTime {
    #[inline(always)]
    pub fn now() -> Self {
        TickTime(SYSTICK.get_tick() as u64)
    }

    #[inline(always)]
    pub fn as_ticks(&self) -> usize {
        // FIXME: there are many places use usize for ticks
        // so we need to convert u64 to usize here temporarily
        // This may cause overflow in long running systems
        // Should be careful in future.
        self.0 as usize
    }

    #[inline(always)]
    pub fn as_millis(&self) -> usize {
        crate::static_assert!(TICKS_PER_SECOND > 0);
        // FIXME: there are many places use usize for millis
        // so we need to convert u64 to usize here temporarily
        ((self.0 * 1000) / (TICKS_PER_SECOND as u64)) as usize
    }

    #[inline(always)]
    pub fn from_ticks(ticks: usize) -> Self {
        // FIXME: there are many places use usize for millis
        // so we need to convert u64 to usize here temporarily
        TickTime(ticks)
    }
}
