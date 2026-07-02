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

/// Kernel delay adapter — implements `embedded_hal::delay::DelayNs`
///
/// Converts nanosecond delays into kernel scheduler operations:
/// sub-tick delays yield the thread; multi-tick delays suspend with timer wakeup.
pub struct KernelDelay;

impl DelayNs for KernelDelay {
    fn delay_ns(&mut self, ns: u32) {
        if !scheduler::is_schedule_ready() {
            #[cfg(target_arch = "riscv32")]
            {
                // rdcycle may not advance on ESP32-C3; spin a fixed count (~ns cycles @ 160MHz).
                let spins = (ns as u64).saturating_mul(160) / 1_000;
                for _ in 0..spins {
                    core::hint::spin_loop();
                }
            }
            #[cfg(not(target_arch = "riscv32"))]
            {
                let _ = ns;
            }
            return;
        }
        let ticks = blueos_kconfig::CONFIG_TICKS_PER_SECOND as u32 * ns / 1_000_000_000;
        if ticks == 0 {
            // yield_me() is a no-op in single-task shell; spin so wait_busy gets a real budget.
            #[cfg(target_arch = "riscv32")]
            {
                let spins = (ns as u64).saturating_mul(160) / 1_000;
                for _ in 0..spins {
                    core::hint::spin_loop();
                }
            }
            #[cfg(not(target_arch = "riscv32"))]
            {
                scheduler::yield_me();
            }
        } else {
            scheduler::suspend_me_for::<()>(Tick(ticks as usize), None);
        }
    }
}

#[cfg(target_arch = "riscv32")]
#[allow(dead_code)]
#[inline]
fn read_cycle() -> u64 {
    let hi: u32;
    let lo: u32;
    unsafe {
        core::arch::asm!(
            "rdcycle {lo}",
            "rdcycleh {hi}",
            hi = out(reg) hi,
            lo = out(reg) lo,
            options(nostack, nomem),
        );
    }
    ((hi as u64) << 32) + lo as u64
}
