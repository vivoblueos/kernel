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

use crate::{
    errno::SysCallFailed,
    syscall::{Sys, Syscall},
};
pub use blueos_header::syscalls::NR::{Close, Read};
use blueos_scal::bk_syscall;
use core::slice;
use libc::{c_int, c_void, size_t, ssize_t};
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn write(fd: i32, buf: *const u8, size: usize) -> isize {
    let buf = unsafe { slice::from_raw_parts(buf, size) };
    Sys::write(fd, buf)
        .map(|bytes| bytes as isize)
        .syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/close.html>.
#[no_mangle]
pub extern "C" fn close(fildes: c_int) -> c_int {
    Sys::close(fildes).map(|_| 0).syscall_failed()
}

/// See https://pubs.opengroup.org/onlinepubs/9799919799/functions/read.html
#[no_mangle]
pub unsafe extern "C" fn read(fildes: c_int, buf: *const c_void, nbyte: size_t) -> ssize_t {
    let buf = unsafe { slice::from_raw_parts_mut(buf as *mut u8, nbyte) };
    Sys::read(fildes, buf)
        .map(|bytes| bytes as ssize_t)
        .syscall_failed()
}
