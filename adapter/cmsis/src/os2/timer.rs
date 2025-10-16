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

use crate::{bridge_utils, os_adapter, MAX_NAME_LEN};
use alloc::boxed::Box;
use blueos::{
    irq,
    time::timer::{Timer, TimerEntry},
    types::{Arc, ArcInner, Uint},
};
use cmsis_os2::*;
use core::{
    mem::{self, ManuallyDrop},
    ptr,
};
use delegate::delegate;

os_adapter! {
    "timer" => OsTimer: Timer,
}

impl OsTimer {
    delegate! {
        to self.inner() {
            pub fn is_activated(&self) -> bool;
            pub fn start(&self);
            pub fn start_new_interval(&self, interval: usize);
            pub fn stop(&self);
            pub fn reset(&self);
        }
    }
}

// Create and Initialize a timer.
// \param[in]     func          function pointer to callback function.
// \param[in]     timer_type    \ref osTimerOnce for one-shot or \ref osTimerPeriodic for periodic behavior.
// \param[in]     argument      argument to the timer callback function.
// \param[in]     attr          timer attributes; NULL: default values.
// \return timer ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osTimerNew(
    func: osTimerFunc_t,
    timer_type: osTimerType_t,
    argument: *mut core::ffi::c_void,
    attr: *const osTimerAttr_t,
) -> osTimerId_t {
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    let Some(func) = func else {
        return ptr::null_mut();
    };

    if ((timer_type != osTimerType_t_osTimerOnce) && (timer_type != osTimerType_t_osTimerPeriodic))
    {
        return ptr::null_mut();
    }

    let entry = TimerEntry::C(func, argument);
    let timer = if timer_type == osTimerType_t_osTimerOnce {
        Timer::new_hard_oneshot(0, entry)
    } else {
        Timer::new_hard_periodic(0, entry)
    };

    if attr.is_null() {
        // Use default values when attr is NULL
        let os_timer = Arc::new(OsTimer::with_default_name(timer));
        return Arc::into_raw(os_timer) as osTimerId_t;
    }

    let attr_ref = unsafe { &*attr };

    if attr_ref.cb_mem.is_null() {
        // Allocate memory dynamically
        let os_timer = Arc::new(OsTimer::with_name(timer, attr_ref.name));
        return Arc::into_raw(os_timer) as osTimerId_t;
    }
    // Check if cb_size is sufficient when cb_mem is provided
    if attr_ref.cb_size < mem::size_of::<ArcInner<OsTimer>>() as u32 {
        return ptr::null_mut();
    }

    // Use provided memory;
    unsafe {
        ptr::write(
            attr_ref.cb_mem as *mut ArcInner<OsTimer>,
            ArcInner::const_new(OsTimer::with_name(timer, attr_ref.name)),
        )
    };
    let os_timer = unsafe { Arc::from_raw(attr_ref.cb_mem as *mut _ as *mut OsTimer) };

    (unsafe { Arc::into_raw(os_timer) }) as osTimerId_t
}

// Get name of a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerNew.
// \return name as null-terminated string.
#[no_mangle]
pub extern "C" fn osTimerGetName(timer_id: osTimerId_t) -> *const core::ffi::c_char {
    if timer_id.is_null() {
        return ptr::null();
    }

    let timer = unsafe { ManuallyDrop::new(Arc::from_raw(timer_id as *const OsTimer)) };
    timer.name_bytes().as_ptr() as *const core::ffi::c_char
}

// Start or restart a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerNew.
// \param[in]     ticks         \ref CMSIS_RTOS_TimeOutValue "time ticks" value of the timer.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStart(timer_id: osTimerId_t, ticks: u32) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if timer_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let timer = unsafe { ManuallyDrop::new(Arc::from_raw(timer_id as *const OsTimer)) };

    timer.start_new_interval(ticks as usize);
    osStatus_t_osOK
}

// Stop a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerStop(timer_id: osTimerId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if timer_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let timer = unsafe { ManuallyDrop::new(Arc::from_raw(timer_id as *const OsTimer)) };
    timer.stop();

    osStatus_t_osOK
}

// Check if a timer is running.
// \param[in]     timer_id      timer ID obtained by \ref osTimerNew.
// \return 0 not running, 1 running.
#[no_mangle]
pub extern "C" fn osTimerIsRunning(timer_id: osTimerId_t) -> u32 {
    if irq::is_in_irq() {
        return 0;
    }
    if timer_id.is_null() {
        return 0;
    }

    let timer = unsafe { ManuallyDrop::new(Arc::from_raw(timer_id as *const OsTimer)) };
    if timer.is_activated() {
        return 1;
    }
    0
}

// Delete a timer.
// \param[in]     timer_id      timer ID obtained by \ref osTimerNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osTimerDelete(timer_id: osTimerId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if timer_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    // let timer = unsafe { ManuallyDrop::new(Arc::from_raw(timer_id as *const OsTimer)) };
    // timer.reset();

    let _ = unsafe { Arc::from_raw(timer_id as *mut OsTimer) };
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc, Layout};
    use blueos::{scheduler, time};
    use blueos_test_macro::test;
    use core::{
        ffi::CStr,
        sync::atomic::{AtomicUsize, Ordering},
    };

    unsafe extern "C" fn test_timer(arg: *mut core::ffi::c_void) {
        if arg.is_null() {
            return;
        }
        let counter = ManuallyDrop::new(Arc::from_raw(arg as *const AtomicUsize));
        counter.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn test_os_timer_new() {
        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerOnce,
            core::ptr::null_mut(),
            core::ptr::null(),
        );
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);

        let attr = osTimerAttr_t {
            name: "timer1".as_ptr() as *const core::ffi::c_char,
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
        };

        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerPeriodic,
            core::ptr::null_mut(),
            &attr,
        );
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);

        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };

        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerOnce,
            core::ptr::null_mut(),
            &attr,
        );
        assert!(!timer_id.is_null());
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_timer_get_name() {
        let attr = osTimerAttr_t {
            name: "timer02".as_ptr() as *const core::ffi::c_char,
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
        };

        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerPeriodic,
            core::ptr::null_mut(),
            &attr,
        );
        assert!(!timer_id.is_null());

        let name = osTimerGetName(timer_id);
        assert!(!name.is_null());
        assert_eq!(
            unsafe { CStr::from_ptr(osTimerGetName(timer_id)) }
                .to_str()
                .unwrap(),
            "timer02"
        );
        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_timer_start_once() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };

        let counter = Arc::new(AtomicUsize::new(0));
        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerOnce,
            Arc::into_raw(counter.clone()) as *mut core::ffi::c_void,
            &attr,
        );
        assert!(!timer_id.is_null());
        assert_eq!(osTimerIsRunning(timer_id), 0);

        let result = osTimerStart(timer_id, 8);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 1);
        scheduler::suspend_me_for(20);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_timer_start_periodic() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };
        let counter = Arc::new(AtomicUsize::new(0));

        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerPeriodic,
            Arc::into_raw(counter.clone()) as *mut core::ffi::c_void,
            &attr,
        );
        assert!(!timer_id.is_null());
        assert_eq!(osTimerIsRunning(timer_id), 0);
        let result = osTimerStart(timer_id, 10);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 1);
        scheduler::suspend_me_for(25);

        assert_eq!(counter.load(Ordering::Relaxed), 2);

        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 0);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_timer_stop() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };
        let counter = Arc::new(AtomicUsize::new(0));
        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerPeriodic,
            Arc::into_raw(counter.clone()) as *mut core::ffi::c_void,
            &attr,
        );
        assert!(!timer_id.is_null());
        assert_eq!(osTimerIsRunning(timer_id), 0);

        let result = osTimerStart(timer_id, 9);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 1);
        scheduler::suspend_me_for(25);
        assert_eq!(counter.load(Ordering::Relaxed), 2);
        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 0);

        // TODO: support restart
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: "timer03".as_ptr() as *const core::ffi::c_char,
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };

        let timer_id = osTimerNew(
            Some(test_timer),
            osTimerType_t_osTimerPeriodic,
            Arc::into_raw(counter.clone()) as *mut core::ffi::c_void,
            &attr,
        );
        assert!(!timer_id.is_null());
        assert_eq!(osTimerIsRunning(timer_id), 0);
        let result = osTimerStart(timer_id, 10);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 1);
        scheduler::suspend_me_for(25);
        assert_eq!(counter.load(Ordering::Relaxed), 4);

        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 0);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    unsafe extern "C" fn test_timer1(arg: *mut core::ffi::c_void) {
        if arg.is_null() {
            return;
        }

        let raw_ptr = arg as *mut i32;
        unsafe { *raw_ptr += 10 };
    }

    #[test]
    fn test_os_timer_start_callback() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsTimer>>(), 8).unwrap();
        let attr = osTimerAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };
        let mut val = 50;
        let arg = Box::into_raw(Box::new(val)) as *mut core::ffi::c_void;
        let timer_id = osTimerNew(Some(test_timer1), osTimerType_t_osTimerPeriodic, arg, &attr);
        assert!(!timer_id.is_null());
        assert_eq!(osTimerIsRunning(timer_id), 0);

        let result = osTimerStart(timer_id, 8);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osTimerIsRunning(timer_id), 1);
        scheduler::suspend_me_for(20);

        let result = osTimerStop(timer_id);
        assert_eq!(result, osStatus_t_osOK);
        let res = unsafe {
            let boxed = Box::from_raw(arg as *mut i32);
            *boxed
        };
        assert_eq!(res, val + 20);

        let result = osTimerDelete(timer_id);
        assert_eq!(result, osStatus_t_osOK);
    }
}
