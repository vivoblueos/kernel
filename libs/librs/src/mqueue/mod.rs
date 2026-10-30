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

use crate::{
    errno::SysCallFailed,
    syscall::{Sys, Syscall},
};
use core::ptr;
use libc::{c_char, c_int, c_long, c_uint, mode_t, size_t, timespec};

#[repr(C)]
pub struct mq_attr {
    pub mq_flags: c_long,
    pub mq_maxmsg: c_long,
    pub mq_msgsize: c_long,
    pub mq_curmsgs: c_long,
    pub pad: [c_long; 4],
}

#[no_mangle]
pub extern "C" fn mq_close(mq: c_int) -> c_int {
    Sys::close(mq).map(|_| 0).syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_open(
    name: *const c_char,
    oflag: c_int,
    mode: mode_t,
    attr: *const mq_attr,
) -> c_int {
    let canonical = unsafe {
        if name.read() == b'/' as c_char {
            name.add(1)
        } else {
            name
        }
    };

    Sys::mq_open(canonical, oflag, mode, attr)
        .map(|fd| fd as c_int)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_unlink(name: *const c_char) -> c_int {
    let canonical = unsafe {
        if name.read() == b'/' as c_char {
            name.add(1)
        } else {
            name
        }
    };
    unsafe { Sys::mq_unlink(canonical) }
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_getattr(mqdes: c_int, attr: *mut mq_attr) -> c_int {
    if attr.is_null() {
        return -1;
    }
    Sys::mq_getsetattr(mqdes, ptr::null_mut(), attr)
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_setattr(mqdes: c_int, new: *const mq_attr, old: *mut mq_attr) -> c_int {
    Sys::mq_getsetattr(mqdes, new as *mut mq_attr, old)
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_send(
    mqdes: c_int,
    msg_ptr: *const c_char,
    msg_len: size_t,
    msg_prio: c_uint,
) -> c_int {
    Sys::mq_timedsend(mqdes, msg_ptr, msg_len, msg_prio, ptr::null())
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_timedsend(
    mqdes: c_int,
    msg_ptr: *const c_char,
    msg_len: size_t,
    msg_prio: c_uint,
    timeout: *const timespec,
) -> c_int {
    Sys::mq_timedsend(mqdes, msg_ptr, msg_len, msg_prio, timeout)
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_receive(
    mqdes: c_int,
    msg_ptr: *mut c_char,
    msg_len: size_t,
    msg_prio: *mut c_uint,
) -> c_int {
    Sys::mq_timedsend(mqdes, msg_ptr, msg_len, *msg_prio, ptr::null())
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn mq_timedreceive(
    mqdes: c_int,
    msg_ptr: *mut c_char,
    msg_len: size_t,
    msg_prio: *mut c_uint,
    timeout: *const timespec,
) -> c_int {
    Sys::mq_timedreceive(mqdes, msg_ptr, msg_len, msg_prio, timeout)
        .map(|_| 0)
        .syscall_failed()
}
