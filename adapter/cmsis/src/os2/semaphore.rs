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

use crate::common_objects::OsSemaphore;
use blueos::{
    irq,
    scheduler::{self, InsertModeTrait, InsertToEnd},
    sync::semaphore::Semaphore,
    types::{Arc, ArcInner, Uint},
};
use cmsis_os2::*;
use core::{mem, ptr};

const SEM_WAIT_ERROR: i32 = -1;

// Create and Initialize a Semaphore object.
// \param[in]     max_count     maximum number of available tokens.
// \param[in]     initial_count initial number of available tokens.
// \param[in]     attr          semaphore attributes; NULL: default values.
// \return semaphore ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osSemaphoreNew(
    max_count: u32,
    initial_count: u32,
    attr: *const osSemaphoreAttr_t,
) -> osSemaphoreId_t {
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    // Note: only support 32-bit target temporarily
    if initial_count > Uint::MAX as u32 || initial_count > max_count {
        return ptr::null_mut();
    }

    let semaphore = Arc::new(Semaphore::new());
    if attr.is_null() {
        // Use default values when attr is NULL
        let os_sem = Arc::new(OsSemaphore::with_default_name(semaphore));
        os_sem.init(initial_count as Uint);
        return Arc::into_raw(os_sem) as osSemaphoreId_t;
    }

    let attr_ref = unsafe { &*attr };

    if attr_ref.cb_mem.is_null() {
        // Allocate memory dynamically
        let os_sem = if attr_ref.name.is_null() {
            Arc::new(OsSemaphore::with_default_name(semaphore))
        } else {
            Arc::new(OsSemaphore::with_name(semaphore, attr_ref.name))
        };
        os_sem.init(initial_count as Uint);
        return Arc::into_raw(os_sem) as osSemaphoreId_t;
    }

    // Check if cb_size is sufficient when cb_mem is provided
    if attr_ref.cb_size < mem::size_of::<ArcInner<OsSemaphore>>() as u32 {
        return ptr::null_mut();
    }

    // Use provided memory;
    unsafe {
        ptr::write(
            attr_ref.cb_mem as *mut ArcInner<OsSemaphore>,
            ArcInner::new(OsSemaphore::with_name(semaphore, attr_ref.name)),
        )
    };
    let os_sem = unsafe { Arc::from_raw(attr_ref.cb_mem as *mut _ as *mut OsSemaphore) };
    os_sem.init(initial_count as Uint);

    (unsafe { Arc::into_raw(os_sem) }) as osSemaphoreId_t
}

// Get name of a Semaphore object.
// \param[in]     semaphore_id  semaphore ID obtained by \ref osSemaphoreNew.
// \return name as null-terminated string.
#[no_mangle]
pub extern "C" fn osSemaphoreGetName(semaphore_id: osSemaphoreId_t) -> *const core::ffi::c_char {
    if semaphore_id.is_null() {
        return ptr::null();
    }

    let semaphore: &OsSemaphore = unsafe { &*(semaphore_id as *const OsSemaphore) };
    semaphore.name_bytes().as_ptr() as *const core::ffi::c_char
}

// Acquire a Semaphore token or timeout if no tokens are available.
// \param[in]     semaphore_id  semaphore ID obtained by \ref osSemaphoreNew.
// \param[in]     timeout       \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osSemaphoreAcquire(semaphore_id: osSemaphoreId_t, timeout: u32) -> osStatus_t {
    if irq::is_in_irq() && timeout != 0 {
        return osStatus_t_osErrorISR;
    }
    if semaphore_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let semaphore = unsafe { &*(semaphore_id as *const OsSemaphore) };
    if timeout == 0 {
        if !semaphore.acquire_notimeout::<InsertToEnd>() {
            return osStatus_t_osError;
        }
    } else if !semaphore.acquire_timeout::<InsertToEnd>(timeout as usize) {
        return osStatus_t_osErrorResource;
    }
    osStatus_t_osOK
}

// Release a Semaphore token up to the initial maximum count.
// \param[in]     semaphore_id  semaphore ID obtained by \ref osSemaphoreNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osSemaphoreRelease(semaphore_id: osSemaphoreId_t) -> osStatus_t {
    if semaphore_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let semaphore = unsafe { &*(semaphore_id as *const OsSemaphore) };
    semaphore.release();
    osStatus_t_osOK
}

// Get current Semaphore token count.
// \param[in]     semaphore_id  semaphore ID obtained by \ref osSemaphoreNew.
// \return number of tokens available.
#[no_mangle]
pub extern "C" fn osSemaphoreGetCount(semaphore_id: osSemaphoreId_t) -> u32 {
    if semaphore_id.is_null() {
        return 0;
    }

    let semaphore = unsafe { &*(semaphore_id as *const OsSemaphore) };

    semaphore.count() as u32
}

// Delete a Semaphore object.
// \param[in]     semaphore_id  semaphore ID obtained by \ref osSemaphoreNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osSemaphoreDelete(semaphore_id: osSemaphoreId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if semaphore_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let _ = unsafe { Arc::from_raw(semaphore_id as *mut OsSemaphore) };
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc, Layout};
    use blueos_test_macro::test;
    use core::ffi::CStr;

    #[test]
    fn test_os_semaphore_new() {
        let semaphore_id = osSemaphoreNew(127, 10, ptr::null());
        assert!(!semaphore_id.is_null());
        assert_eq!(osSemaphoreGetCount(semaphore_id), 10);
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_new_with_name() {
        let attr = osSemaphoreAttr_t {
            name: "sem01".as_ptr() as *const core::ffi::c_char,
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
        };
        let semaphore_id = osSemaphoreNew(127, 10, &attr);
        assert!(!semaphore_id.is_null());
        assert_eq!(
            unsafe { CStr::from_ptr(osSemaphoreGetName(semaphore_id)) }
                .to_str()
                .unwrap(),
            "sem01"
        );
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_new_with_given_mem() {
        let layout = Layout::from_size_align(mem::size_of::<ArcInner<OsSemaphore>>(), 8).unwrap();
        let attr = osSemaphoreAttr_t {
            attr_bits: 0,
            name: ptr::null(),
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
        };
        let semaphore_id = osSemaphoreNew(127, 10, &attr);
        assert!(!semaphore_id.is_null());
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_new_count_too_large() {
        let semaphore_id = osSemaphoreNew(10, 42, ptr::null());
        assert!(semaphore_id.is_null());
    }

    #[test]
    fn test_os_semaphore_get_name() {
        let semaphore_id = osSemaphoreNew(127, 10, ptr::null());
        let name = osSemaphoreGetName(semaphore_id);
        assert!(!name.is_null());
        println!(
            "semaphore name: {:?}",
            unsafe { CStr::from_ptr(name) }.to_str().unwrap()
        );
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_acquire() {
        let semaphore_id = osSemaphoreNew(127, 10, ptr::null());

        // Test semaphore acquire without timeout
        let result1 = osSemaphoreAcquire(semaphore_id, 0);
        assert_eq!(result1, osStatus_t_osOK);
        assert_eq!(osSemaphoreGetCount(semaphore_id), 9);

        // Test semaphore acquire with timeout
        let result2 = osSemaphoreAcquire(semaphore_id, 1000);
        assert_eq!(result2, osStatus_t_osOK);
        assert_eq!(osSemaphoreGetCount(semaphore_id), 8);

        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_release() {
        let semaphore_id = osSemaphoreNew(127, 10, ptr::null());

        let result1 = osSemaphoreRelease(semaphore_id);
        assert_eq!(result1, osStatus_t_osOK);
        assert_eq!(osSemaphoreGetCount(semaphore_id), 11);

        let result2 = osSemaphoreRelease(semaphore_id);
        assert_eq!(result2, osStatus_t_osOK);
        assert_eq!(osSemaphoreGetCount(semaphore_id), 12);

        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_get_count() {
        let semaphore_id = osSemaphoreNew(127, 42, ptr::null());
        assert_eq!(osSemaphoreGetCount(semaphore_id), 42);
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_delete() {
        let semaphore_id = osSemaphoreNew(127, 10, ptr::null());
        let result = osSemaphoreDelete(semaphore_id);
        assert_eq!(result, osStatus_t_osOK);
    }
}
