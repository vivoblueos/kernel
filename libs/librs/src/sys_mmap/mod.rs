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
    errno::{Errno, SysCallFailed, ERRNO},
    syscall::{Sys, Syscall},
};
use libc::{c_int, c_void, off_t, size_t};

pub const PROT_READ: c_int = 0x0001;
pub const PROT_WRITE: c_int = 0x0002;
pub const PROT_EXEC: c_int = 0x0004;
pub const PROT_NONE: c_int = 0x0000;

pub const MAP_SHARED: c_int = 0x0001;
pub const MAP_PRIVATE: c_int = 0x0002;
pub const MAP_ANONYMOUS: c_int = 0x0020;

pub const MAP_FAILED: *mut c_void = usize::wrapping_neg(1) as *mut c_void;

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/mmap.html>.
/// This is not valid for blueos now , but is provided for malloc implementation.
#[no_mangle]
pub unsafe extern "C" fn mmap(
    addr: *mut c_void,
    len: size_t,
    prot: c_int,
    flags: c_int,
    fildes: c_int,
    off: off_t,
) -> *mut c_void {
    match Sys::mmap(addr, len, prot, flags, fildes, off) {
        Ok(ptr) => ptr,
        Err(Errno(errno)) => {
            ERRNO.set(errno);
            MAP_FAILED
        }
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/munmap.html>.
/// This is not valid for blueos now , but is provided for compatibility with linux emulation applications.
#[no_mangle]
pub unsafe extern "C" fn munmap(addr: *mut c_void, len: size_t) -> c_int {
    Sys::munmap(addr, len).map(|()| 0).syscall_failed()
}
