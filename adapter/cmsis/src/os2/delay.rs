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

use blueos::{irq, scheduler, time};
use cmsis_os2::*;

#[no_mangle]
pub extern "C" fn osDelay(ticks: u32) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    scheduler::suspend_me_for(ticks as usize);
    osStatus_t_osOK
}

#[no_mangle]
pub extern "C" fn osDelayUntil(ticks: u32) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    let current_tick = time::get_sys_ticks() as u32;
    let delay = ticks - current_tick;
    if delay == 0 || delay > 0x7fffffff {
        return osStatus_t_osErrorParameter;
    }
    scheduler::suspend_me_for(delay as usize);
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    #[test]
    fn test_os_delay() {
        // This test is a placeholder. Actual testing would require a proper environment setup.
        let current_tick = time::get_sys_ticks() as u32;
        let result = osDelay(10);
        assert_eq!(result, osStatus_t_osOK);
        let new_tick = time::get_sys_ticks() as u32;
        assert!(new_tick >= current_tick + 10);
    }

    #[test]
    fn test_os_delay_until() {
        let current_tick = time::get_sys_ticks() as u32;
        let result = osDelayUntil(current_tick + 20);
        assert_eq!(result, osStatus_t_osOK);
        let new_tick = time::get_sys_ticks() as u32;
        assert!(new_tick >= current_tick + 20);
    }
}
