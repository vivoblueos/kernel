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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

#![deny(unsafe_op_in_unsafe_fn)]
use crate::{
    c_str::CStr,
    errno::{SysCallFailed, ERRNO},
    syscall::{Sys, Syscall},
};

use blueos_header::syscalls::NR::{Fcntl, Open};
use blueos_scal::bk_syscall;
use libc::{
    c_char, c_int, c_long, c_ulonglong, mode_t, F_DUPFD, F_GETLK, F_SETFD, F_SETFL, F_SETLK,
    F_SETLKW, O_CREAT, O_TRUNC, O_WRONLY,
};

#[no_mangle]
pub unsafe extern "C" fn creat(path: *const c_char, mode: mode_t) -> c_int {
    unsafe { open(path, O_WRONLY | O_CREAT | O_TRUNC, mode) }
}

#[no_mangle]
pub unsafe extern "C" fn fcntl(fildes: c_int, cmd: c_int, mut __valist: ...) -> c_int {
    // c_ulonglong
    let arg = match cmd {
        F_DUPFD | F_SETFD | F_SETFL | F_SETLK | F_SETLKW | F_GETLK => unsafe {
            __valist.arg::<c_ulonglong>()
        },
        _ => 0,
    };

    Sys::fcntl(fildes, cmd, arg as usize)
        .map(|e| e as c_int)
        .syscall_failed()
}

// https://pubs.opengroup.org/onlinepubs/9799919799/functions/open.html
#[no_mangle]
pub unsafe extern "C" fn open(path: *const c_char, oflag: c_int, mut __valist: ...) -> c_int {
    let mode = if oflag & O_CREAT == O_CREAT {
        // SAFETY: The caller must ensure that the mode is valid.
        // We assume that the caller has passed a valid mode_t value.
        // The actual value of mode is extracted from the variadic arguments.

        unsafe { __valist.arg::<mode_t>() }
    } else {
        0
    };
    // open syscall result not mapped in blueos or other os
    // just simply convert the result
    let fd = bk_syscall!(Open, path, oflag, mode) as c_int;
    if fd < 0 {
        ERRNO.set(-fd);
        return -1;
    }
    fd
}
