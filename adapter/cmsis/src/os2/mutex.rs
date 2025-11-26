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

use crate::common_objects::OsMutex;
use blueos::{
    irq,
    sync::mutex::Mutex,
    types::{Arc, ArcInner, Int},
};
use cmsis_os2::*;
use core::{
    mem::{self, ManuallyDrop},
    ptr,
};
use log;

// Create and Initialize a Mutex object.
// \param[in]     attr          mutex attributes; NULL: default values.
// \return mutex ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osMutexNew(attr: *const osMutexAttr_t) -> osMutexId_t {
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    let mutex = Mutex::create();

    if attr.is_null() {
        // Use default values when attr is NULL
        let os_mutex = Arc::new(OsMutex::with_default_name(mutex));
        return Arc::into_raw(os_mutex) as osMutexId_t;
    }

    let attr_ref = unsafe { &*attr };
    if attr_ref.cb_mem.is_null() {
        // Allocate memory dynamically
        let os_mutex = if attr_ref.name.is_null() {
            Arc::new(OsMutex::with_default_name(mutex))
        } else {
            Arc::new(OsMutex::with_name(mutex, attr_ref.name))
        };
        return Arc::into_raw(os_mutex) as osMutexId_t;
    }

    // Check if cb_size is sufficient when cb_mem is provided
    if attr_ref.cb_size < mem::size_of::<ArcInner<OsMutex>>() as u32 {
        return ptr::null_mut();
    }

    // Use provided memory
    if attr_ref.name.is_null() {
        unsafe {
            ptr::write(
                attr_ref.cb_mem as *mut ArcInner<OsMutex>,
                ArcInner::new(OsMutex::with_default_name(mutex)),
            )
        }
    } else {
        unsafe {
            ptr::write(
                attr_ref.cb_mem as *mut ArcInner<OsMutex>,
                ArcInner::new(OsMutex::with_name(mutex, attr_ref.name)),
            )
        }
    }
    (unsafe { Arc::into_raw(Arc::from_raw(attr_ref.cb_mem as *mut ArcInner<OsMutex>)) })
        as osMutexId_t
}

// Get name of a Mutex object.
// \param[in]     mutex_id      mutex ID obtained by \ref osMutexNew.
// \return name as null-terminated string.
#[no_mangle]
pub extern "C" fn osMutexGetName(mutex_id: osMutexId_t) -> *const core::ffi::c_char {
    if mutex_id.is_null() {
        return ptr::null();
    }

    let mutex = unsafe { ManuallyDrop::new(Arc::from_raw(mutex_id as *const OsMutex)) };
    mutex.name_bytes().as_ptr() as *const core::ffi::c_char
}

/// Acquire a Mutex or timeout if it is locked.
// \param[in]     mutex_id      mutex ID obtained by \ref osMutexNew.
// \param[in]     timeout       \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMutexAcquire(mutex_id: osMutexId_t, timeout: u32) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mutex_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let mutex = unsafe { ManuallyDrop::new(Arc::from_raw(mutex_id as *const OsMutex)) };
    if !mutex.pend_for(timeout as usize) {
        return osStatus_t_osErrorResource;
    }
    osStatus_t_osOK
}

// Release a Mutex that was acquired by \ref osMutexAcquire.
// \param[in]     mutex_id      mutex ID obtained by \ref osMutexNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMutexRelease(mutex_id: osMutexId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mutex_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let mutex = unsafe { ManuallyDrop::new(Arc::from_raw(mutex_id as *const OsMutex)) };
    mutex.post();
    osStatus_t_osOK
}

// Get Thread which owns a Mutex object.
// \param[in]     mutex_id      mutex ID obtained by \ref osMutexNew.
// \return thread ID of owner thread or NULL when mutex was not acquired.
#[no_mangle]
pub extern "C" fn osMutexGetOwner(mutex_id: osMutexId_t) -> osThreadId_t {
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    if mutex_id.is_null() {
        return ptr::null_mut();
    }

    let mutex = unsafe { ManuallyDrop::new(Arc::from_raw(mutex_id as *const OsMutex)) };
    if let Some(owner) = mutex.owner() {
        if let Some(alien_ptr) = owner.get_alien_ptr() {
            return alien_ptr.as_ptr() as osThreadId_t;
        }
    }
    log::warn!("not a cmsis thread");
    ptr::null_mut()
}

// Delete a Mutex object.
// \param[in]     mutex_id      mutex ID obtained by \ref osMutexNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMutexDelete(mutex_id: osMutexId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mutex_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let _ = unsafe { Arc::from_raw(mutex_id as *mut OsMutex) };
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc, Layout};
    use blueos_test_macro::test;
    use core::ffi::CStr;

    #[test]
    fn test_os_mutex_new() {
        let mutex_id = osMutexNew(ptr::null());
        assert!(!mutex_id.is_null());
        assert!(osMutexGetOwner(mutex_id).is_null());
        let result = osMutexDelete(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_new_with_name() {
        let attr = osMutexAttr_t {
            name: "mutex01".as_ptr() as *const core::ffi::c_char,
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
        };
        let mutex_id = osMutexNew(&attr);
        assert!(!mutex_id.is_null());
        assert_eq!(
            unsafe { CStr::from_ptr(osMutexGetName(mutex_id)) }
                .to_str()
                .unwrap(),
            "mutex01"
        );
        let result = osMutexDelete(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_new_with_given_mem() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsMutex>>(), 8).unwrap();
        let attr = osMutexAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };
        let mutex_id = osMutexNew(&attr);
        assert!(!mutex_id.is_null());

        unsafe { dealloc(attr.cb_mem as *mut u8, layout) };
    }

    #[test]
    fn test_os_mutex_get_name() {
        let mutex_id = osMutexNew(ptr::null());
        let name = osMutexGetName(mutex_id);
        assert!(!name.is_null());
        println!(
            "mutex name: {:?}",
            unsafe { CStr::from_ptr(name) }.to_str().unwrap()
        );
        let result = osMutexDelete(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_acquire() {
        let mutex_id = osMutexNew(ptr::null());

        let result = osMutexAcquire(mutex_id, 0);
        assert_eq!(result, osStatus_t_osOK);
        // assert_eq!(osMutexGetOwner(mutex_id), osThreadGetId());

        let result = osMutexAcquire(mutex_id, 0);
        assert_eq!(result, osStatus_t_osOK);
        // assert_eq!(osMutexGetOwner(mutex_id), osThreadGetId());

        let result = osMutexDelete(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_release() {
        let mutex_id = osMutexNew(ptr::null());
        let result = osMutexAcquire(mutex_id, 0);
        assert_eq!(result, osStatus_t_osOK);
        // assert_eq!(osMutexGetOwner(mutex_id), osThreadGetId());

        let result = osMutexAcquire(mutex_id, 0);
        assert_eq!(result, osStatus_t_osOK);

        let result = osMutexRelease(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
        // assert_eq!(osMutexGetOwner(mutex_id), osThreadGetId());

        let result = osMutexRelease(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
        assert!(osMutexGetOwner(mutex_id).is_null());

        let result = osMutexDelete(mutex_id);
        assert_eq!(result, osStatus_t_osOK);
    }
}
