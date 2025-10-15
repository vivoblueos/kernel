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

use alloc::boxed::Box;
use blueos::{
    time,
    time::timer::{Timer, TimerEntry},
    types::{Arc, Int, Uint},
};
use cmsis_os::*;
use core::{
    ffi::c_void,
    mem::{self, ManuallyDrop},
    ptr,
    sync::atomic::{AtomicUsize, Ordering},
};

// Create a timer.
// \param[in]     timer_def     timer object referenced with \ref osTimer.
// \param[in]     timer_type    osTimerOnce for one-shot or osTimerPeriodic for periodic behavior.
// \param[in]     argument      argument to the timer call back function.
// \return timer ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osTimerCreate(
    timer_def: *const osTimerDef_t,
    timer_type: os_timer_type,
    argument: *const c_void,
) -> osTimerId {
    if timer_def.is_null() {
        return core::ptr::null_mut();
    }
    let timer_def = unsafe { &*timer_def };

    let Some(func) = timer_def.ptimer else {
        return core::ptr::null_mut();
    };

    if ((timer_type != os_timer_type_osTimerOnce) && (timer_type != os_timer_type_osTimerPeriodic))
    {
        return core::ptr::null_mut();
    }

    let entry = TimerEntry::C(
        unsafe {
            core::mem::transmute::<
                unsafe extern "C" fn(*const c_void),
                unsafe extern "C" fn(*mut c_void),
            >(func)
        },
        argument as *mut c_void,
    );
    let timer = if timer_type == os_timer_type_osTimerOnce {
        Timer::new_hard_oneshot(0, entry)
    } else {
        Timer::new_hard_periodic(0, entry)
    };
    let os_timer = Arc::into_raw(timer);
    os_timer as osTimerId
}

// Start or restart a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \param[in]     millisec      \ref CMSIS_RTOS_TimeOutValue "Time delay" value of the timer.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStart(timer_id: osTimerId, millisec: u32) -> osStatus {
    if timer_id.is_null() {
        return osStatus_osErrorParameter;
    }

    let timer = unsafe { &*(timer_id as *const Timer) };
    timer.start_new_interval(millisec as usize);
    osStatus_osOK
}

// Stop the timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStop(timer_id: osTimerId) -> osStatus {
    if timer_id.is_null() {
        return osStatus_osErrorParameter;
    }
    let timer = unsafe { &*(timer_id as *const Timer) };
    timer.stop();
    osStatus_osOK
}

// Delete a timer that was created by \ref osTimerCreate.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerDelete(timer_id: osTimerId) -> osStatus {
    if timer_id.is_null() {
        return osStatus_osErrorParameter;
    }

    let _ = unsafe { Arc::from_raw(timer_id as *mut Timer) };
    osStatus_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::{scheduler, time};
    use blueos_test_macro::test;

    unsafe extern "C" fn test_timer(arg: *const c_void) {
        if arg.is_null() {
            return;
        }
        let counter = ManuallyDrop::new(Arc::<AtomicUsize>::from_raw(arg as *const AtomicUsize));
        counter.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn test_os_timer_create() {
        let timer_def = osTimerDef_t {
            ptimer: Some(test_timer),
            timer: core::ptr::null_mut(),
        };

        let timer_id = osTimerCreate(&timer_def, os_timer_type_osTimerOnce, core::ptr::null());
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);

        let timer_id = osTimerCreate(&timer_def, os_timer_type_osTimerPeriodic, core::ptr::null());
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
    }

    #[test]
    fn test_os_timer_start_once() {
        let timer_def = osTimerDef_t {
            ptimer: Some(test_timer),
            timer: core::ptr::null_mut(),
        };

        let counter = Arc::new(AtomicUsize::new(0));
        let timer_id = osTimerCreate(
            &timer_def,
            os_timer_type_osTimerOnce,
            Arc::into_raw(counter.clone()) as *mut c_void,
        );
        assert!(!timer_id.is_null());

        let result = osTimerStart(timer_id, 5);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for(20);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
    }

    #[test]
    fn test_os_timer_start_periodic() {
        let timer_def = osTimerDef_t {
            ptimer: Some(test_timer),
            timer: core::ptr::null_mut(),
        };
        let counter = Arc::new(AtomicUsize::new(0));
        let timer_id = osTimerCreate(
            &timer_def,
            os_timer_type_osTimerPeriodic,
            Arc::into_raw(counter.clone()) as *mut c_void,
        );
        assert!(!timer_id.is_null());

        let result = osTimerStart(timer_id, 5);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for(23);
        assert_eq!(counter.load(Ordering::Relaxed), 4);

        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_osOK);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
    }

    #[test]
    fn test_os_timer_stop() {
        let timer_def = osTimerDef_t {
            ptimer: Some(test_timer),
            timer: core::ptr::null_mut(),
        };
        let counter = Arc::new(AtomicUsize::new(0));
        let timer_id = osTimerCreate(&timer_def, os_timer_type_osTimerOnce, core::ptr::null());
        assert!(!timer_id.is_null());

        let result = osTimerStart(timer_id, 5);
        assert_eq!(result, osStatus_osOK);

        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_osOK);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
        assert_eq!(counter.load(Ordering::Relaxed), 0);

        let timer_id = osTimerCreate(
            &timer_def,
            os_timer_type_osTimerPeriodic,
            Arc::into_raw(counter.clone()) as *mut c_void,
        );
        assert!(!timer_id.is_null());

        let result = osTimerStart(timer_id, 5);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for(23);
        assert_eq!(counter.load(Ordering::Relaxed), 4);
        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_osOK);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
    }
}
