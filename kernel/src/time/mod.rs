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

pub(crate) mod systick;
pub(crate) mod timer;

use crate::{arch, boards, scheduler, support::DisableInterruptGuard, thread::Thread};
use blueos_kconfig::TICKS_PER_SECOND;
use systick::SYSTICK;

pub const WAITING_FOREVER: usize = usize::MAX;

pub fn systick_init(sys_clock: u32) -> bool {
    SYSTICK.init(sys_clock, TICKS_PER_SECOND as u32)
}

pub fn get_sys_ticks() -> usize {
    SYSTICK.get_tick()
}

pub fn get_sys_cycles() -> u64 {
    SYSTICK.get_cycles()
}

pub(crate) fn get_cycles_to_duration(cycles: u64) -> core::time::Duration {
    boards::get_cycles_to_duration(cycles)
}

pub(crate) fn get_cycles_to_ms(cycles: u64) -> u64 {
    boards::get_cycles_to_ms(cycles)
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
    need_schedule = scheduler::handle_tick_increment(1) || need_schedule;
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

pub fn tick_get_millisecond() -> usize {
    crate::static_assert!(TICKS_PER_SECOND > 0);
    crate::static_assert!(1000 % TICKS_PER_SECOND == 0);

    get_sys_ticks() * (1000 / TICKS_PER_SECOND)
}
