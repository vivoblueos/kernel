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

// Define constants that will be exported to C
// These match the extern const declarations in cmsis_os.h
#[no_mangle]
pub static os_tickfreq: u32 = TICKS_PER_SECOND as u32; // System timer frequency in Hz

/// Get the RTOS kernel system timer counter.
/// \return RTOS kernel system timer as 32-bit value
/// uint32_t osKernelSysTick (void);
#[no_mangle]
pub extern "C" fn osKernelSysTick() -> u32 {
    time::get_sys_ticks() as u32
}


#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_osKernelSysTick() {
        let tick = osKernelSysTick();
        assert!(tick > 0);
    }
}