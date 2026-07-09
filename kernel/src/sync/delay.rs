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

use crate::{scheduler, time::Tick};
use embedded_hal::delay::DelayNs;

/// ESP32-C3 CPU clock. The systimer (`ClockImpl::hz()` = 16MHz) is not the CPU clock.
#[cfg(target_board = "seeed_xiao_esp32c3")]
const CPU_HZ: u32 = 160_000_000;

/// Kernel delay adapter — implements `embedded_hal::delay::DelayNs`
///
/// Converts nanosecond delays into kernel scheduler operations:
/// sub-tick delays yield the thread; multi-tick delays suspend with timer wakeup.
pub struct KernelDelay;

impl DelayNs for KernelDelay {
    fn delay_ns(&mut self, ns: u32) {
        let ticks = ((blueos_kconfig::CONFIG_TICKS_PER_SECOND as u64) * (ns as u64) / 1_000_000_000)
            as usize;
        if !scheduler::is_schedule_ready() {
            let wait_t = Tick::after(Tick(ticks as usize));
            while !wait_t.is_elapsed() {
                core::hint::spin_loop();
            }
            return;
        }

        if ticks == 0 {
            scheduler::yield_me();
        } else {
            scheduler::suspend_me_for::<()>(Tick(ticks as usize), None);
        }
    }
}
