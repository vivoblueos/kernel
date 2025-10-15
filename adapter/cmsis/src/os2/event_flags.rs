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

use crate::common_objects::OsEventFlags;
use blueos::{
    error::{code, Error},
    irq,
    scheduler::InsertToEnd,
    sync::event_flags::{EventFlags, EventFlagsMode},
    time,
    types::{Arc, ArcInner},
};
use cmsis_os2::*;
use core::{
    mem, ptr,
    sync::atomic::{compiler_fence, Ordering},
};

fn os_event_flags_error(e: Error) -> u32 {
    match e {
        code::EINVAL => osFlagsErrorParameter,
        code::ETIMEDOUT => osFlagsErrorTimeout,
        _ => osFlagsError,
    }
}

// Create and Initialize an Event Flags object.
// \param[in]     attr          event flags attributes; NULL: default values.
// \return event flags ID for reference by other functions or NULL in case of error.
// osEventFlagsId_t osEventFlagsNew (const osEventFlagsAttr_t *attr);
#[no_mangle]
pub extern "C" fn osEventFlagsNew(attr: *const osEventFlagsAttr_t) -> osEventFlagsId_t {
    // Check if the current context is an IRQ handler
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    let event_flags = Arc::new(EventFlags::new());
    event_flags.init(0);

    if attr.is_null() {
        // Use default values when attr is NULL
        let os_event = Arc::new(OsEventFlags::with_default_name(event_flags));
        os_event.init(0);
        return Arc::into_raw(os_event) as osEventFlagsId_t;
    }

    let attr_ref = unsafe { &*attr };
    if attr_ref.cb_mem.is_null() {
        // Allocate memory dynamically
        let os_event = if attr_ref.name.is_null() {
            Arc::new(OsEventFlags::with_default_name(event_flags))
        } else {
            Arc::new(OsEventFlags::with_name(event_flags, attr_ref.name))
        };
        os_event.init(0);
        return Arc::into_raw(os_event) as osEventFlagsId_t;
    }

    // Check if cb_size is sufficient when cb_mem is provided
    if attr_ref.cb_size < mem::size_of::<ArcInner<OsEventFlags>>() as u32 {
        return ptr::null_mut();
    }

    // Use provided memory;
    unsafe {
        ptr::write(
            attr_ref.cb_mem as *mut ArcInner<OsEventFlags>,
            ArcInner::const_new(OsEventFlags::with_name(event_flags, attr_ref.name)),
        )
    };
    let os_event = unsafe { Arc::from_raw(attr_ref.cb_mem as *mut _ as *mut OsEventFlags) };
    os_event.init(0);
    Arc::into_raw(os_event) as osEventFlagsId_t
}

// Get name of an Event Flags object.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \return name as null-terminated string.
// const char *osEventFlagsGetName (osEventFlagsId_t ef_id);
#[no_mangle]
pub extern "C" fn osEventFlagsGetName(ef_id: osEventFlagsId_t) -> *const core::ffi::c_char {
    if ef_id.is_null() {
        return ptr::null();
    }

    let event_flags: &OsEventFlags = unsafe { &*(ef_id as *const _ as *const OsEventFlags) };
    event_flags.name_bytes().as_ptr() as *const core::ffi::c_char
}

// Set the specified Event Flags.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \param[in]     flags         specifies the flags that shall be set.
// \return event flags after setting or error code if highest bit set.
// uint32_t osEventFlagsSet (osEventFlagsId_t ef_id, uint32_t flags);
#[no_mangle]
pub extern "C" fn osEventFlagsSet(ef_id: osEventFlagsId_t, flags: u32) -> u32 {
    if ef_id.is_null() {
        return osFlagsErrorParameter;
    }

    let event_flags: &OsEventFlags = unsafe { &*(ef_id as *const _ as *const OsEventFlags) };
    match event_flags.set(flags) {
        Ok(new_flags) => new_flags,
        Err(e) => os_event_flags_error(e),
    }
}

// Clear the specified Event Flags.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \param[in]     flags         specifies the flags that shall be cleared.
// \return event flags before clearing or error code if highest bit set.
// uint32_t osEventFlagsClear (osEventFlagsId_t ef_id, uint32_t flags);
#[no_mangle]
pub extern "C" fn osEventFlagsClear(ef_id: osEventFlagsId_t, flags: u32) -> u32 {
    if ef_id.is_null() {
        return osFlagsErrorParameter;
    }

    let event_flags: &OsEventFlags = unsafe { &*(ef_id as *const _ as *const OsEventFlags) };
    event_flags.clear(flags)
}

// Get the current Event Flags.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \return current event flags.
// uint32_t osEventFlagsGet (osEventFlagsId_t ef_id);
#[no_mangle]
pub extern "C" fn osEventFlagsGet(ef_id: osEventFlagsId_t) -> u32 {
    if ef_id.is_null() {
        // Return 0 if ef_id is null, as per CMSIS-RTOS2 specification.
        return 0;
    }

    let event_flags: &OsEventFlags = unsafe { &*(ef_id as *const _ as *const OsEventFlags) };
    event_flags.get()
}

// Wait for one or more Event Flags to become signaled.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \param[in]     flags         specifies the flags to wait for.
// \param[in]     options       specifies flags options (osFlagsXxxx).
// \param[in]     timeout       \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return event flags before clearing or error code if highest bit set.
// uint32_t osEventFlagsWait (osEventFlagsId_t ef_id, uint32_t flags, uint32_t options, uint32_t timeout);
#[no_mangle]
pub extern "C" fn osEventFlagsWait(
    ef_id: osEventFlagsId_t,
    flags: u32,
    options: u32,
    timeout: u32,
) -> u32 {
    if irq::is_in_irq() && timeout != 0 {
        return osFlagsErrorParameter;
    }
    if ef_id.is_null() {
        return osFlagsErrorParameter;
    }

    let mut mode = EventFlagsMode::ANY;
    if options & osFlagsWaitAll != 0 {
        mode = EventFlagsMode::ALL;
    }
    if options & osFlagsNoClear == 0 {
        mode |= EventFlagsMode::NO_CLEAR;
    }

    let event_flags: &OsEventFlags = unsafe { &*(ef_id as *const _ as *const OsEventFlags) };
    match event_flags.wait::<InsertToEnd>(
        flags,
        mode,
        if timeout == osWaitForever {
            time::WAITING_FOREVER as usize
        } else {
            timeout as usize
        },
    ) {
        Ok(prev_flags) => prev_flags,
        Err(e) => os_event_flags_error(e),
    }
}

// Delete an Event Flags object.
// \param[in]     ef_id         event flags ID obtained by \ref osEventFlagsNew.
// \return status code that indicates the execution status of the function.
// osStatus_t osEventFlagsDelete (osEventFlagsId_t ef_id);
#[no_mangle]
pub extern "C" fn osEventFlagsDelete(ef_id: osEventFlagsId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if ef_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let _ = unsafe { Arc::from_raw(ef_id as *mut OsEventFlags) }; // Drop the event flags object.
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc, Layout};
    use blueos_test_macro::test;

    #[test]
    fn test_os_event_flags_new() {
        let ef_id = osEventFlagsNew(ptr::null());
        assert!(!ef_id.is_null());
        osEventFlagsDelete(ef_id);
    }

    #[test]
    fn test_os_event_flags_new_with_attr() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsEventFlags>>(), 8).unwrap();
        let attr = osEventFlagsAttr_t {
            attr_bits: 0,
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
            name: ptr::null(),
        };
        let ef_id = osEventFlagsNew(&attr);
        assert!(!ef_id.is_null());
        osEventFlagsDelete(ef_id);
    }

    #[test]
    fn test_os_event_flags_set() {
        let ef_id = osEventFlagsNew(ptr::null());
        assert!(!ef_id.is_null());
        let result = osEventFlagsSet(ef_id, 1);
        assert_eq!(result, 1);
        osEventFlagsDelete(ef_id);
    }

    #[test]
    fn test_os_event_flags_clear() {
        let ef_id = osEventFlagsNew(ptr::null());
        assert!(!ef_id.is_null());
        let result = osEventFlagsSet(ef_id, 1);
        assert_eq!(result, 1);
        let result = osEventFlagsClear(ef_id, 1);
        assert_eq!(result, 1);
        let result = osEventFlagsGet(ef_id);
        assert_eq!(result, 0);
        osEventFlagsDelete(ef_id);
    }

    #[test]
    fn test_os_event_flags_get() {
        let ef_id = osEventFlagsNew(ptr::null());
        assert!(!ef_id.is_null());
        let result = osEventFlagsGet(ef_id);
        assert_eq!(result, 0);
        osEventFlagsDelete(ef_id);
    }

    #[test]
    fn test_os_event_flags_wait() {
        let ef_id = osEventFlagsNew(ptr::null());
        assert!(!ef_id.is_null());
        let result = osEventFlagsSet(ef_id, 1);
        assert_eq!(result, 1);
        let result = osEventFlagsWait(ef_id, 1, osFlagsWaitAll, 0);
        assert_eq!(result, 1);
        osEventFlagsDelete(ef_id);
    }
}
