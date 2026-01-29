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
    time::{
        timer,
        timer::{Repeat, Timer, TimerCallback, TimerMode},
        timer_manager::Iou,
        Tick,
    },
    types::{Arc, Int, Uint},
};
use cmsis_os::*;
use core::{
    ffi::c_void,
    mem::{self, ManuallyDrop},
    ptr::NonNull,
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
    argument: *mut c_void,
) -> osTimerId {
    if timer_def.is_null() {
        return core::ptr::null_mut();
    }
    let timer_def = unsafe { &*timer_def };

    let Some(func) = timer_def.ptimer else {
        return core::ptr::null_mut();
    };

    let mut tm = Timer::new();
    #[allow(non_upper_case_globals)]
    match timer_type {
        os_timer_type_osTimerOnce => tm.mode = TimerMode::Deadline(Tick::MAX),
        os_timer_type_osTimerPeriodic => tm.mode = TimerMode::Repeat(Repeat::default()),
        _ => return core::ptr::null_mut(),
    }

    let func: unsafe extern "C" fn(*mut c_void) = unsafe { core::mem::transmute(func) };

    tm.callback = TimerCallback::UnsafePosix(func, argument);
    let os_timer = Box::into_raw(Box::new(tm));

    os_timer as osTimerId
}

// Start or restart a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \param[in]     millisec      \ref CMSIS_RTOS_TimeOutValue "Time delay" value of the timer.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStart(timer_id: osTimerId, millis: u32) -> osStatus {
    let Some(mut os_timer) = NonNull::new(timer_id as *mut Timer) else {
        return osStatus_osErrorParameter;
    };

    let tm_mut = unsafe { os_timer.as_mut() };
    let mut duration = Tick::from_millis(millis as u64);
    // To avoid endless clock interrupt.
    if duration == Tick(0) {
        duration = Tick(1);
    }
    let base = Tick::after(duration);

    match &mut tm_mut.mode {
        TimerMode::Deadline(d) => *d = base,
        TimerMode::Repeat(r) => {
            r.base_deadline = base;
            r.period = duration;
        }
    }
    timer::add_hard_timer(tm_mut);

    osStatus_osOK
}

// Stop the timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStop(timer_id: osTimerId) -> osStatus {
    let Some(mut os_timer) = NonNull::new(timer_id as *mut Timer) else {
        return osStatus_osErrorParameter;
    };

    let tm_mut = unsafe { os_timer.as_mut() };
    let iou = unsafe { Iou::from_mut(tm_mut) };
    timer::remove_hard_timer(iou);

    osStatus_osOK
}

// Delete a timer that was created by \ref osTimerCreate.
// \param[in]     timer_id      timer ID obtained by \ref osTimerCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerDelete(timer_id: osTimerId) -> osStatus {
    let Some(mut os_timer) = NonNull::new(timer_id as *mut Timer) else {
        return osStatus_osErrorParameter;
    };

    let _ = unsafe { Box::from_raw(os_timer.as_ptr()) };
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

        let timer_id = osTimerCreate(&timer_def, os_timer_type_osTimerOnce, core::ptr::null_mut());
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);

        let timer_id = osTimerCreate(
            &timer_def,
            os_timer_type_osTimerPeriodic,
            core::ptr::null_mut(),
        );
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

        let result = osTimerStart(timer_id, 50);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for::<()>(Tick::from_millis(50), None);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
        let result = osTimerStop(timer_id);

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

        let result = osTimerStart(timer_id, 50);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for::<()>(Tick::from_millis(50 * 4), None);
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
        let timer_id = osTimerCreate(&timer_def, os_timer_type_osTimerOnce, core::ptr::null_mut());
        assert!(!timer_id.is_null());

        let result = osTimerStart(timer_id, 50);
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

        let result = osTimerStart(timer_id, 50);
        assert_eq!(result, osStatus_osOK);

        scheduler::suspend_me_for::<()>(Tick::from_millis(50 * 4), None);
        assert_eq!(counter.load(Ordering::Relaxed), 4);
        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_osOK);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_osOK);
    }
}
