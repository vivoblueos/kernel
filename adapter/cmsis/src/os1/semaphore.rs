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

use blueos::{
    scheduler::InsertToEnd,
    sync::semaphore::Semaphore,
    time::Tick,
    types::{Arc, Int, Uint},
};
use cmsis_os::*;

const SEM_WAIT_ERROR: i32 = -1;

// Create and Initialize a Semaphore object used for managing resources.
// \param[in]     semaphore_def semaphore definition referenced with \ref osSemaphore.
// \param[in]     count         number of available resources.
// \return semaphore ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osSemaphoreCreate(
    semaphore_def: *const osSemaphoreDef_t,
    count: i32,
) -> osSemaphoreId {
    // Note: only support 32-bit target temporarily
    if count < 0 || count > Int::MAX as i32 || count > osFeature_Semaphore as i32 {
        return core::ptr::null_mut();
    }

    let semaphore = Arc::new(Semaphore::new());
    semaphore.init(count as Uint);
    let semaphore_raw = Arc::into_raw(semaphore);
    semaphore_raw as osSemaphoreId
}

// Get semaphore count, return 0 if error
fn __osSemaphoreGetCount(semaphore_id: osSemaphoreId) -> i32 {
    if semaphore_id.is_null() {
        return 0;
    }
    let semaphore = unsafe { &*(semaphore_id as *const Semaphore) };

    semaphore.count() as i32
}

// Wait until a Semaphore token becomes available.
// \param[in]     semaphore_id  semaphore object referenced with \ref osSemaphoreCreate.
// \param[in]     millis      \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return number of available tokens, or -1 in case of incorrect parameters.
#[no_mangle]
#[allow(clippy::collapsible_else_if)]
pub extern "C" fn osSemaphoreWait(semaphore_id: osSemaphoreId, millis: u32) -> i32 {
    if semaphore_id.is_null() {
        return SEM_WAIT_ERROR;
    }
    let semaphore = unsafe { &*(semaphore_id as *const Semaphore) };
    if millis == 0 {
        if !semaphore.acquire_notimeout::<InsertToEnd>() {
            return SEM_WAIT_ERROR;
        }
    } else {
        if !semaphore.acquire_timeout::<InsertToEnd>(Tick::from_millis(millis as u64)) {
            return SEM_WAIT_ERROR;
        }
    }
    __osSemaphoreGetCount(semaphore_id)
}

// Release a Semaphore token.
// \param[in]     semaphore_id  semaphore object referenced with \ref osSemaphoreCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osSemaphoreRelease(semaphore_id: osSemaphoreId) -> osStatus {
    if semaphore_id.is_null() {
        return osStatus_osErrorParameter;
    }
    let semaphore = unsafe { &*(semaphore_id as *const Semaphore) };
    semaphore.release();
    osStatus_osOK
}

// Delete a Semaphore that was created by \ref osSemaphoreCreate.
// \param[in]     semaphore_id  semaphore object referenced with \ref osSemaphoreCreate.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osSemaphoreDelete(semaphore_id: osSemaphoreId) -> osStatus {
    if semaphore_id.is_null() {
        return osStatus_osErrorParameter;
    }
    let _ = unsafe { Arc::from_raw(semaphore_id as *mut Semaphore) };
    osStatus_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_os_semaphore_create() {
        let semaphore_id = osSemaphoreCreate(core::ptr::null(), 5);
        assert!(!semaphore_id.is_null());
        assert_eq!(__osSemaphoreGetCount(semaphore_id), 5);
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_wait() {
        let semaphore_id = osSemaphoreCreate(core::ptr::null(), 2);
        let result1 = osSemaphoreWait(semaphore_id, 0);
        assert_eq!(result1, 1);
        let result2 = osSemaphoreWait(semaphore_id, 1000);
        assert_eq!(result2, 0);
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_release() {
        let semaphore_id = osSemaphoreCreate(core::ptr::null(), 5);
        let result1 = osSemaphoreRelease(semaphore_id);
        assert_eq!(result1, osStatus_osOK);
        assert_eq!(__osSemaphoreGetCount(semaphore_id), 6);
        let result2 = osSemaphoreRelease(semaphore_id);
        assert_eq!(result2, osStatus_osOK);
        assert_eq!(__osSemaphoreGetCount(semaphore_id), 7);
        osSemaphoreDelete(semaphore_id);
    }

    #[test]
    fn test_os_semaphore_release_wait_failed() {
        let result1 = osSemaphoreWait(core::ptr::null_mut(), 0);
        assert_eq!(result1, SEM_WAIT_ERROR);
        let result2 = osSemaphoreRelease(core::ptr::null_mut());
        assert_eq!(result2, osStatus_osErrorParameter)
    }

    #[test]
    fn test_os_semaphore_delete() {
        let semaphore_id = osSemaphoreCreate(core::ptr::null(), 5);
        let result = osSemaphoreDelete(semaphore_id);
        assert_eq!(result, osStatus_osOK);
    }
}
