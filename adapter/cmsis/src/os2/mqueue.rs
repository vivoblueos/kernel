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

use crate::common_objects::OsMessageQueue;
use alloc::slice;
use blueos::{
    error::{code, Error},
    irq,
    sync::mqueue::{MessageQueue, SendMode},
    time::Tick,
    types::{Arc, ArcInner, Int},
};
use cmsis_os2::*;
use core::{
    mem::{self, ManuallyDrop},
    ptr,
};

// Create and Initialize a Message Queue object.
// \param[in]     msg_count     maximum number of messages in queue.
// \param[in]     msg_size      maximum message size in bytes.
// \param[in]     attr          message queue attributes; NULL: default values.
// \return message queue ID for reference by other functions or NULL in case of error.
#[no_mangle]
pub extern "C" fn osMessageQueueNew(
    msg_count: u32,
    msg_size: u32,
    attr: *const osMessageQueueAttr_t,
) -> osMessageQueueId_t {
    if irq::is_in_irq() {
        return ptr::null_mut();
    }
    if msg_count == 0 || msg_size == 0 {
        return ptr::null_mut();
    }

    if attr.is_null() {
        let queue = Arc::new(MessageQueue::new(
            msg_size as usize,
            msg_count,
            core::ptr::null_mut(),
        ));
        queue.init();
        // Use default values when attr is NULL
        let os_queue = Arc::new(OsMessageQueue::with_default_name(queue));
        return Arc::into_raw(os_queue) as osMessageQueueId_t;
    }

    let attr_ref = unsafe { &*attr };
    let queue = if attr_ref.mq_mem.is_null() {
        Arc::new(MessageQueue::new(
            msg_size as usize,
            msg_count,
            core::ptr::null_mut(),
        ))
    } else {
        if attr_ref.mq_size < ((msg_size + core::mem::size_of::<usize>() as u32) * msg_count) {
            return ptr::null_mut();
        }
        Arc::new(MessageQueue::new(
            msg_size as usize,
            msg_count,
            attr_ref.mq_mem as *mut u8,
        ))
    };

    queue.init();
    if attr_ref.cb_mem.is_null() {
        // Allocate memory dynamically
        let os_queue = if attr_ref.name.is_null() {
            Arc::new(OsMessageQueue::with_default_name(queue))
        } else {
            Arc::new(OsMessageQueue::with_name(queue, attr_ref.name))
        };
        return Arc::into_raw(os_queue) as osMessageQueueId_t;
    }

    // Check if cb_size is sufficient when cb_mem is provided
    if attr_ref.cb_size < mem::size_of::<ArcInner<OsMessageQueue>>() as u32 {
        return ptr::null_mut();
    }

    // Use provided memory
    if attr_ref.name.is_null() {
        unsafe {
            ptr::write(
                attr_ref.cb_mem as *mut ArcInner<OsMessageQueue>,
                ArcInner::new(OsMessageQueue::with_default_name(queue)),
            )
        }
    } else {
        unsafe {
            ptr::write(
                attr_ref.cb_mem as *mut ArcInner<OsMessageQueue>,
                ArcInner::new(OsMessageQueue::with_name(queue, attr_ref.name)),
            )
        }
    };

    (unsafe {
        Arc::into_raw(Arc::from_raw(
            attr_ref.cb_mem as *mut ArcInner<OsMessageQueue>,
        ))
    }) as osMessageQueueId_t
}

// Get name of a Message Queue object.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return name as null-terminated string.
#[no_mangle]
pub extern "C" fn osMessageQueueGetName(mq_id: osMessageQueueId_t) -> *const core::ffi::c_char {
    if mq_id.is_null() {
        return ptr::null();
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    queue.name_bytes().as_ptr() as *const core::ffi::c_char
}

// Put a Message into a Queue or timeout if Queue is full.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \param[in]     msg_ptr       pointer to buffer with message to put into a queue.
// \param[in]     msg_prio      message priority.
// \param[in]     timeout       \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMessageQueuePut(
    mq_id: osMessageQueueId_t,
    msg_ptr: *const core::ffi::c_void,
    msg_prio: u8,
    timeout: u32,
) -> osStatus_t {
    if irq::is_in_irq() && timeout != 0 {
        return osStatus_t_osErrorISR;
    }
    if mq_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    let (size, _) = queue.node_info();
    let msg_size = size - core::mem::size_of::<usize>();
    let buffer = unsafe { slice::from_raw_parts(msg_ptr as *const u8, msg_size) };
    match queue.send(buffer, msg_size, Tick(timeout as usize), SendMode::Normal) {
        Ok(_) => osStatus_t_osOK,
        Err(e) => {
            if e == code::ETIMEDOUT {
                osStatus_t_osErrorTimeout
            } else {
                osStatus_t_osError
            }
        }
    }
}

// Get a Message from a Queue or timeout if Queue is empty.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \param[out]    msg_ptr       pointer to buffer for message to get from a queue.
// \param[out]    msg_prio      pointer to buffer for message priority or NULL.
// \param[in]     timeout       \ref CMSIS_RTOS_TimeOutValue or 0 in case of no time-out.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMessageQueueGet(
    mq_id: osMessageQueueId_t,
    msg_ptr: *mut core::ffi::c_void,
    msg_prio: *mut u8,
    timeout: u32,
) -> osStatus_t {
    if mq_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    let (size, _) = queue.node_info();
    let msg_size = size - core::mem::size_of::<usize>();
    let mut buffer = unsafe { slice::from_raw_parts_mut(msg_ptr as *mut u8, msg_size) };
    match queue.recv(buffer, msg_size, Tick(timeout as usize)) {
        Ok(_) => osStatus_t_osOK,
        Err(e) => {
            if e == code::ETIMEDOUT {
                osStatus_t_osErrorTimeout
            } else {
                osStatus_t_osError
            }
        }
    }
}

// Get maximum number of messages in a Message Queue.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return maximum number of messages.
#[no_mangle]
pub extern "C" fn osMessageQueueGetCapacity(mq_id: osMessageQueueId_t) -> u32 {
    if mq_id.is_null() {
        return 0;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    let (_, count) = queue.node_info();
    count
}

// Get maximum message size in a Memory Pool.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return maximum message size in bytes.
#[no_mangle]
pub extern "C" fn osMessageQueueGetMsgSize(mq_id: osMessageQueueId_t) -> u32 {
    if mq_id.is_null() {
        return 0;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    let (msg_size, _) = queue.node_info();
    (msg_size - core::mem::size_of::<usize>()) as u32
}

// Get number of queued messages in a Message Queue.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return number of queued messages.
#[no_mangle]
pub extern "C" fn osMessageQueueGetCount(mq_id: osMessageQueueId_t) -> u32 {
    if mq_id.is_null() {
        return 0;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    queue.recvable_count()
}

// Get number of available slots for messages in a Message Queue.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return number of available slots for messages.
#[no_mangle]
pub extern "C" fn osMessageQueueGetSpace(mq_id: osMessageQueueId_t) -> u32 {
    if mq_id.is_null() {
        return 0;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    queue.sendable_count()
}

// Reset a Message Queue to initial empty state.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMessageQueueReset(mq_id: osMessageQueueId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mq_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let queue = unsafe { ManuallyDrop::new(Arc::from_raw(mq_id as *const OsMessageQueue)) };
    queue.reset();
    osStatus_t_osOK
}

// Delete a Message Queue object.
// \param[in]     mq_id         message queue ID obtained by \ref osMessageQueueNew.
// \return status code that indicates the execution status of the function.
#[no_mangle]
pub extern "C" fn osMessageQueueDelete(mq_id: osMessageQueueId_t) -> osStatus_t {
    if irq::is_in_irq() {
        return osStatus_t_osErrorISR;
    }
    if mq_id.is_null() {
        return osStatus_t_osErrorParameter;
    }

    let _ = unsafe { Arc::from_raw(mq_id as *mut OsMessageQueue) };
    osStatus_t_osOK
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc, Layout};
    use blueos::support::align_up_size;
    use blueos_test_macro::test;
    use core::ffi::CStr;

    #[test]
    fn test_os_mqueue_new() {
        let queue_id = osMessageQueueNew(5, 4, ptr::null());
        assert!(!queue_id.is_null());
        let node_size = align_up_size(4, core::mem::size_of::<usize>());
        assert_eq!(
            (
                osMessageQueueGetCapacity(queue_id),
                osMessageQueueGetMsgSize(queue_id)
            ),
            (5, node_size as u32)
        );
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (0, 5)
        );
        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mqueue_new_with_name() {
        let attr = osMessageQueueAttr_t {
            name: "queue01".as_ptr() as *const core::ffi::c_char,
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
            mq_mem: ptr::null_mut(),
            mq_size: 0,
        };
        let queue_id = osMessageQueueNew(5, 4, &attr);
        assert!(!queue_id.is_null());
        let node_size = align_up_size(4, core::mem::size_of::<usize>());
        assert_eq!(
            (
                osMessageQueueGetCapacity(queue_id),
                osMessageQueueGetMsgSize(queue_id)
            ),
            (5, node_size as u32)
        );
        assert_eq!(
            unsafe { CStr::from_ptr(osMessageQueueGetName(queue_id)) }
                .to_str()
                .unwrap(),
            "queue01"
        );
        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_queue_new_with_given_cb_mem() {
        let layout =
            Layout::from_size_align(mem::size_of::<ArcInner<OsMessageQueue>>(), 8).unwrap();
        let attr = osMessageQueueAttr_t {
            name: ptr::null(),
            attr_bits: 0,
            cb_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            cb_size: layout.size() as u32,
            mq_mem: ptr::null_mut(),
            mq_size: 0,
        };
        let queue_id = osMessageQueueNew(5, 4, &attr);
        assert!(!queue_id.is_null());
        let node_size = align_up_size(4, core::mem::size_of::<usize>());
        assert_eq!(
            (
                osMessageQueueGetCapacity(queue_id),
                osMessageQueueGetMsgSize(queue_id)
            ),
            (5, node_size as u32)
        );
        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_queue_new_with_given_mq_mem() {
        let size = 4;
        let count = 5;
        let node_size = align_up_size(size, core::mem::size_of::<usize>());
        let total_size = count * (node_size + core::mem::size_of::<usize>());
        let layout = Layout::from_size_align(total_size, 8).unwrap();
        let attr = osMessageQueueAttr_t {
            name: ptr::null(),
            attr_bits: 0,
            cb_mem: ptr::null_mut(),
            cb_size: 0,
            mq_mem: unsafe { alloc(layout) as *mut core::ffi::c_void },
            mq_size: layout.size() as u32,
        };
        let queue_id = osMessageQueueNew(count as u32, size as u32, &attr);
        assert!(!queue_id.is_null());
        assert_eq!(
            (
                osMessageQueueGetCapacity(queue_id),
                osMessageQueueGetMsgSize(queue_id)
            ),
            (count as u32, node_size as u32)
        );
    }

    #[test]
    fn test_os_queue_get_name() {
        let queue_id = osMessageQueueNew(5, 4, ptr::null());
        let name = osMessageQueueGetName(queue_id);
        assert!(!name.is_null());
        println!(
            "queue name: {:?}",
            unsafe { CStr::from_ptr(name) }.to_str().unwrap()
        );
        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_send() {
        let queue_id = osMessageQueueNew(2, 4, ptr::null());

        let buffer = [1u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (1, 1)
        );

        let buffer = [3u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (2, 0)
        );

        let buffer = [5u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_ne!(result, osStatus_t_osOK);

        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_queue_recv() {
        let queue_id = osMessageQueueNew(2, 4, ptr::null());

        let buffer = [1u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (1, 1)
        );

        let buffer = [3u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (2, 0)
        );

        let mut buffer = [0u8; 4];
        let result = osMessageQueueGet(
            queue_id,
            buffer.as_mut_ptr() as *mut core::ffi::c_void,
            core::ptr::null_mut(),
            0,
        );
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (1, 1)
        );

        let mut buffer = [0u8; 4];
        let result = osMessageQueueGet(
            queue_id,
            buffer.as_mut_ptr() as *mut core::ffi::c_void,
            core::ptr::null_mut(),
            0,
        );
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(buffer, [3u8, 3u8, 3u8, 3u8]);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (0, 2)
        );

        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }

    #[test]
    fn test_os_mutex_reset() {
        let queue_id = osMessageQueueNew(2, 4, ptr::null());

        let buffer = [1u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (1, 1)
        );

        let buffer = [3u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (2, 0)
        );

        let result = osMessageQueueReset(queue_id);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (0, 2)
        );
        let node_size = align_up_size(4, core::mem::size_of::<usize>());
        assert_eq!(
            (
                osMessageQueueGetCapacity(queue_id),
                osMessageQueueGetMsgSize(queue_id)
            ),
            (2, node_size as u32)
        );

        let buffer = [1u8; 4];
        let result = osMessageQueuePut(queue_id, buffer.as_ptr() as *const core::ffi::c_void, 0, 0);
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (1, 1)
        );

        let mut buffer = [0u8; 4];
        let result = osMessageQueueGet(
            queue_id,
            buffer.as_mut_ptr() as *mut core::ffi::c_void,
            core::ptr::null_mut(),
            0,
        );
        assert_eq!(result, osStatus_t_osOK);
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(
            (
                osMessageQueueGetCount(queue_id),
                osMessageQueueGetSpace(queue_id)
            ),
            (0, 2)
        );

        let result = osMessageQueueDelete(queue_id);
        assert_eq!(result, osStatus_t_osOK);
    }
}
