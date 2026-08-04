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

/// ESP32-C3/C6 CPU clock. The systimer (`ClockImpl::hz()` = 16MHz) is not the CPU clock.
#[cfg(any(
    target_board = "seeed_xiao_esp32c3",
    target_board = "esp32c6_devkitc_1"
))]

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
            #[cfg(any(
                target_board = "seeed_xiao_esp32c3",
                target_board = "esp32c6_devkitc_1"
            ))]
            {
                // rdcycle may not advance on ESP32-C3/C6; spin ~ns cycles @ CPU_HZ.
                let spins = (ns as u64).saturating_mul(CPU_HZ as u64) / 1_000_000_000;
                for _ in 0..spins {
                    core::hint::spin_loop();
                }
            }
            #[cfg(not(any(
                target_board = "seeed_xiao_esp32c3",
                target_board = "esp32c6_devkitc_1"
            )))]
            {
                let _ = ns;
            }
            return;
        }

        if ticks == 0 {
            // yield_me() is a no-op in single-task shell; spin so wait_busy gets a real budget.
            #[cfg(any(
                target_board = "seeed_xiao_esp32c3",
                target_board = "esp32c6_devkitc_1"
            ))]
            {
                let spins = (ns as u64).saturating_mul(CPU_HZ as u64) / 1_000_000_000;
                for _ in 0..spins {
                    core::hint::spin_loop();
                }
            }
            #[cfg(not(any(
                target_board = "seeed_xiao_esp32c3",
                target_board = "esp32c6_devkitc_1"
            )))]
            {
                scheduler::yield_me();
            }
        } else {
            scheduler::suspend_me_for::<()>(Tick(ticks as usize), None);
        }
    }
}
