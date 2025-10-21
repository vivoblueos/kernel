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

use crate::boards;
use spin::Once;

pub const SYSTICK_IRQ_NUM: IrqNumber = IrqNumber::new(arch::TIMER_INT);
static BOOT_CYCLE_COUNT: Once<u64> = Once::new();
fn get_boot_cycle_count() -> u64 {
    *BOOT_CYCLE_COUNT.call_once(|| boards::current_cycles() as u64)
}

impl Systick {
    pub fn init(&self, _sys_clock: u32, tick_per_second: u32) -> bool {
        let step = 1_000_000_000 / tick_per_second as usize;
        // SAFETY: step is only written once during initialization
        unsafe {
            *self.step.get() = step;
        }
        boards::set_timeout_after(step);
        let _ = get_boot_cycle_count();
        true
    }

    pub fn get_cycles(&self) -> u64 {
        boards::current_cycles() as u64
    }

    pub fn reset_counter(&self) {
        boards::set_timeout_after(self.get_step());
    }
}
