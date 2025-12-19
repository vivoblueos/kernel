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

use blueos::time;
use blueos_kconfig::TICKS_PER_SECOND;

// Get the RTOS kernel tick count.
// \return RTOS kernel current tick count.
// uint32_t osKernelGetTickCount (void);
#[no_mangle]
pub extern "C" fn osKernelGetTickCount() -> u32 {
    time::TickTime::now().as_ticks() as u32
}

// Get the RTOS kernel tick frequency.
// \return frequency of the kernel tick in hertz, i.e. kernel ticks per second.
// uint32_t osKernelGetTickFreq (void);
#[no_mangle]
pub extern "C" fn osKernelGetTickFreq() -> u32 {
    TICKS_PER_SECOND as u32
}

// Get the RTOS kernel system timer count.
// \return RTOS kernel current system timer count as 32-bit value.
// uint32_t osKernelGetSysTimerCount (void);
#[no_mangle]
pub extern "C" fn osKernelGetSysTimerCount() -> u32 {
    time::get_sys_cycles() as u32
}

// Get the RTOS kernel system timer frequency.
// \return frequency of the system timer in hertz, i.e. timer ticks per second.
// uint32_t osKernelGetSysTimerFreq (void);
#[no_mangle]
pub extern "C" fn osKernelGetSysTimerFreq() -> u32 {
    TICKS_PER_SECOND as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_osKernelSysTick() {
        let tick = osKernelGetTickCount();
        assert!(tick > 0);

        let count = osKernelGetSysTimerCount();
        assert!(count > 0);

        let freq = osKernelGetSysTimerFreq();
        assert!(freq > 0);

        let freq = osKernelGetTickFreq();
        assert!(freq > 0);
    }
}
