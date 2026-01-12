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

use blueos::{irq, scheduler, time, time::Tick};
use cmsis_os2::*;
use core::sync::atomic::{AtomicIsize, Ordering};

static KERNEL_STATE: AtomicIsize = AtomicIsize::new(0);
// osKernelState_t_osKernelInactive is represented by 0
// osKernelState_t_osKernelReady is represented by 1
// osKernelState_t_osKernelRunning is represented by 2
// osKernelState_t_osKernelLocked is represented by 3
// osKernelState_t_osKernelSuspended is represented by 4

#[no_mangle]
pub extern "C" fn osKernelInitialize() -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if KERNEL_STATE.load(Ordering::SeqCst) != 0 {
        return osStatus_t_osError;
    }
    // Initialize the kernel
    // it's an code point for blueos kernel able to run applications
    // no-op for blueos kernel

    // Initialize all os2 objects needed mempool
    // no-op for blueos kernel

    // Set the kernel initialized flag
    KERNEL_STATE.store(1, Ordering::SeqCst);
    // Return success status
    osStatus_t_osOK
}

#[no_mangle]
pub extern "C" fn osKernelStart() -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    // Create Idle thread and timer thread
    // no-op for blueos kernel, as it is already in ready queue

    // Enable timer tick interrupt
    // no-op for blueos kernel, as it is already enabled

    // Pick the highest priority thread to run
    // This is a no-op for blueos kernel

    // Set the kernel state to running
    KERNEL_STATE.store(2, Ordering::SeqCst);
    // Return success status
    osStatus_t_osOK
}

#[no_mangle]
pub extern "C" fn osKernelGetState() -> osKernelState_t {
    // Get the current state of the kernel

    let state = KERNEL_STATE.load(Ordering::SeqCst);
    state as osKernelState_t
}

#[no_mangle]
pub unsafe extern "C" fn osKernelGetInfo(
    version: *mut osVersion_t,
    id_buf: *mut core::ffi::c_char,
    id_size: u32,
) -> osStatus_t {
    // Get the kernel information
    if version.is_null() || id_buf.is_null() {
        return osStatus_t_osErrorParameter;
    }

    // Fill in the version information
    (*version).api = 20030000;
    (*version).kernel = 10000000; // v1.0.0?

    // Fill in the kernel ID
    let id_str = c"BlueOS Kernel";
    let id_bytes = id_str.to_bytes();
    let mut effective_id_size = id_bytes.len() as u32;
    if id_size < effective_id_size {
        effective_id_size = id_size;
    }

    core::ptr::copy_nonoverlapping(
        id_bytes.as_ptr(),
        id_buf as *mut u8,
        effective_id_size as usize,
    );
    osStatus_t_osOK
}

// return previous lock state, 0 means no lock, 1 means locked, -1 means error
#[no_mangle]
pub extern "C" fn osKernelLock() -> i32 {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    let mut lock = 0;
    match KERNEL_STATE.load(Ordering::SeqCst) {
        2 => {
            // If the kernel is running, set it to locked
            lock = 0;
            KERNEL_STATE.store(3, Ordering::SeqCst);
            disable_scheduler();
        }
        3 => {
            // If the kernel is already locked, return 1
            lock = 1;
        }
        _ => {
            lock = -1;
        }
    }

    lock
}

#[no_mangle]
pub extern "C" fn osKernelUnlock() -> i32 {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    let mut lock = 0;
    match KERNEL_STATE.load(Ordering::SeqCst) {
        3 => {
            // If the kernel is locked, set it to running
            lock = 1;
            KERNEL_STATE.store(2, Ordering::SeqCst);
            enable_scheduler();
        }
        2 => {
            // If the kernel is already running, return 0
            lock = 0;
        }
        _ => {
            lock = -1;
        }
    }

    lock
}

#[no_mangle]
pub extern "C" fn osKernelRestoreLock(lock: i32) -> i32 {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    let mut lock_new = 0;
    match KERNEL_STATE.load(Ordering::SeqCst) {
        3 => {
            match lock {
                0 => {
                    // If lock is 0, set the kernel state to running
                    KERNEL_STATE.store(2, Ordering::SeqCst);
                    enable_scheduler();
                    lock_new = 0; // Running
                }
                1 => {
                    // If lock is 1, set the kernel state to locked
                    lock_new = 1; // Locked
                }
                _ => {
                    lock_new = -1; // Invalid lock state
                }
            }
        }
        2 => {
            match lock {
                0 => {
                    // If lock is 0, set the kernel state to running
                    lock_new = 0; // Running
                }
                1 => {
                    // If lock is 1, set the kernel state to locked
                    KERNEL_STATE.store(3, Ordering::SeqCst);
                    disable_scheduler();
                    lock_new = 1; // Locked
                }
                _ => {
                    lock_new = -1; // Invalid lock state
                }
            }
        }
        _ => {
            lock_new = -1; // Invalid state
        }
    }
    lock_new
}

// suspend the scheduler, looks like only for idle thread,
// not sure it is useful for blueos kernel
// loop {
//     let mut sleep_ticks = osKernelSuspend();
//     if sleep_ticks  {
//         setup_watchdog();
//         WFE();
//         sleep_ticks = adjust_sleep_ticks();
//     }
//     osKernelResume(sleep_ticks);
// }
#[no_mangle]
pub extern "C" fn osKernelSuspend() -> u32 {
    if irq::is_in_irq() {
        // If called from an interrupt, return 0 indicating no delay
        return 0;
    }
    if KERNEL_STATE.load(Ordering::SeqCst) != 2 {
        // If the kernel is not running, return 0 indicating no delay
        return 0;
    }

    let mut delay = Tick::MAX;

    // Set the kernel state to suspended
    KERNEL_STATE.store(4, Ordering::SeqCst);
    // Disable the scheduler
    disable_scheduler();
    // bypass look for timer thread get max delay
    delay.0 as u32
}

// called in same context as osKernelSuspend
#[no_mangle]
pub extern "C" fn osKernelResume(sleep_ticks: u32) {
    if irq::is_in_irq() {
        return;
    }
    if KERNEL_STATE.load(Ordering::SeqCst) != 4 {
        // If the kernel is not suspended, return immediately
        return;
    }

    // Set the kernel state to running
    KERNEL_STATE.store(2, Ordering::SeqCst);
    enable_scheduler();
    // in fact, we should take sleep_ticks into account
    // but for now, we resume scheduler immediately
}

#[inline]
fn disable_scheduler() {
    // Disable tick interrupt

    // Disable preemption
    let current = scheduler::current_thread();
    current.disable_preempt();
}

#[inline]
fn enable_scheduler() {
    // Enable tick interrupt

    // Enable preemption
    let current = scheduler::current_thread();
    current.enable_preempt();
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_os_kernel_initialize() {
        let result = osKernelInitialize();
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelReady);
    }

    #[test]
    fn test_os_kernel_start() {
        let result = osKernelStart();
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelRunning);
    }

    #[test]
    fn test_os_kernel_lock_unlock() {
        osKernelStart();
        let lock = osKernelLock();
        assert_eq!(lock, 0);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelLocked);
        let unlock = osKernelUnlock();
        assert_eq!(unlock, 1);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelRunning);
    }

    #[test]
    fn test_os_kernel_restore_lock() {
        let lock = osKernelLock();
        assert_eq!(lock, 0);
        let restore = osKernelRestoreLock(1);
        assert_eq!(restore, 1);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelLocked);
        let restore_running = osKernelRestoreLock(0);
        assert_eq!(restore_running, 0);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelRunning);
    }

    #[test]
    fn test_os_kernel_suspend_resume() {
        let suspend = osKernelSuspend();

        assert_eq!(suspend, Tick::MAX.0 as u32);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelSuspended);
        osKernelResume(0);
        assert_eq!(osKernelGetState(), osKernelState_t_osKernelRunning);
    }

    #[test]
    fn test_os_kernel_get_info() {
        let mut version = osVersion_t { api: 0, kernel: 0 };
        let mut id_buf: [u8; 20] = [0; 20];
        let result = unsafe {
            osKernelGetInfo(
                &mut version,
                id_buf.as_mut_ptr() as *mut _,
                id_buf.len() as u32,
            )
        };
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(version.api, 20030000);
        assert_eq!(version.kernel, 10000000);
        let id_str = core::str::from_utf8(&id_buf[..]).unwrap();
        assert_eq!(id_str.trim_end_matches('\0'), "BlueOS Kernel");
    }
}
