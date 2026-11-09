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
    c_str::CStr,
    errno::{Errno, SysCallFailed, ERRNO},
    syscall::{Sys, Syscall},
};
use core::{ptr, slice};
use libc::{c_char, c_int, c_void, gid_t, mode_t, off_t, pid_t, size_t, ssize_t, uid_t, EINVAL};
pub mod io;
pub mod sysconf;
pub use io::*;
pub use sysconf::*;

/// compatible with linux
/// TODO: define stat/statfs struct in newlib, coherent with linux
pub const O_PATH: c_int = 0;
pub const O_NOFOLLOW: c_int = 0o2000000;

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getcwd.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn getcwd(mut buf: *mut c_char, mut size: size_t) -> *mut c_char {
    if buf.is_null() || size == 0 {
        // a little different behavior from posix, we don't alloc memory here
        ERRNO.set(EINVAL);
        return ptr::null_mut();
    }

    match Sys::getcwd(buf, size) {
        Ok(()) => buf,
        Err(Errno(errno)) => {
            ERRNO.set(errno);
            ptr::null_mut()
        }
    }
}
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/access.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn access(path: *const c_char, mode: c_int) -> c_int {
    let path = unsafe { CStr::from_ptr(path) };
    Sys::access(path, mode).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/chdir.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn chdir(path: *const c_char) -> c_int {
    let path = unsafe { CStr::from_ptr(path) };
    Sys::chdir(path).map(|_| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/fdatasync.html>.
#[unsafe(no_mangle)]
pub extern "C" fn fdatasync(fildes: c_int) -> c_int {
    Sys::fdatasync(fildes).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/fsync.html>.
#[unsafe(no_mangle)]
pub extern "C" fn fsync(fildes: c_int) -> c_int {
    Sys::fsync(fildes).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/ftruncate.html>.
#[unsafe(no_mangle)]
pub extern "C" fn ftruncate(fildes: c_int, length: off_t) -> c_int {
    Sys::ftruncate(fildes, length).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/dup.html>.
#[unsafe(no_mangle)]
pub extern "C" fn dup(fildes: c_int) -> c_int {
    Sys::dup(fildes).syscall_failed()
}

/// See https://pubs.opengroup.org/onlinepubs/9799919799/functions/stat.html
#[unsafe(no_mangle)]
pub unsafe extern "C" fn stat(file: *const c_char, buf: *mut c_char) -> c_int {
    let file = unsafe { CStr::from_ptr(file) };

    let fd = Sys::open(file, O_PATH, 0);
    if fd < 0 {
        return -1;
    }

    let res = unsafe { Sys::fstat(fd, buf) }.map(|()| 0).syscall_failed();

    Sys::close(fd);

    res
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn lstat(path: *const c_char, buf: *mut c_char) -> c_int {
    let path = unsafe { CStr::from_ptr(path) };

    let fd = Sys::open(path, O_PATH | O_NOFOLLOW, 0);
    if fd < 0 {
        return -1;
    }

    let res = unsafe { Sys::fstat(fd, buf) }.map(|()| 0).syscall_failed();

    Sys::close(fd);

    res
}

/// See https://pubs.opengroup.org/onlinepubs/9799919799/functions/umask.html
#[unsafe(no_mangle)]
pub extern "C" fn umask(mask: mode_t) -> mode_t {
    Sys::umask(mask)
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/link.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn link(path1: *const c_char, path2: *const c_char) -> c_int {
    let path1 = unsafe { CStr::from_ptr(path1) };
    let path2 = unsafe { CStr::from_ptr(path2) };
    Sys::link(path1, path2).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/pause.html>.
#[unsafe(no_mangle)]
pub extern "C" fn pause() -> c_int {
    Sys::pause().map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/nice.html>.
#[unsafe(no_mangle)]
pub extern "C" fn nice(incr: c_int) -> c_int {
    Sys::nice(incr).map(|val| val as c_int).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/readlink.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn readlink(
    path: *const c_char,
    buf: *mut c_char,
    bufsize: size_t,
) -> ssize_t {
    let path = unsafe { CStr::from_ptr(path) };
    let buf = unsafe { slice::from_raw_parts_mut(buf as *mut u8, bufsize) };
    Sys::readlink(path, buf)
        .map(|read| read as ssize_t)
        .syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/lseek.html>.
#[unsafe(no_mangle)]
pub extern "C" fn lseek(fildes: c_int, offset: off_t, whence: c_int) -> off_t {
    Sys::lseek(fildes, offset, whence)
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/rename.html>.
/// TODO: move to stdio for header file inclusion
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rename(oldpath: *const c_char, newpath: *const c_char) -> c_int {
    let oldpath = unsafe { CStr::from_ptr(oldpath) };
    let newpath = unsafe { CStr::from_ptr(newpath) };
    Sys::rename(oldpath, newpath).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/unlink.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unlink(path: *const c_char) -> c_int {
    let path = unsafe { CStr::from_ptr(path) };
    Sys::unlink(path).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/symlink.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn symlink(path1: *const c_char, path2: *const c_char) -> c_int {
    let path1 = unsafe { CStr::from_ptr(path1) };
    let path2 = unsafe { CStr::from_ptr(path2) };
    Sys::symlink(path1, path2).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sync.html>.
#[unsafe(no_mangle)]
pub extern "C" fn sync() {
    Sys::sync();
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/pipe.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pipe(fildes: *mut c_int) -> c_int {
    Sys::pipe2(unsafe { slice::from_raw_parts_mut(fildes, 2) }, 0)
        .map(|()| 0)
        .syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/pread.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pread(
    fildes: c_int,
    buf: *mut c_void,
    nbyte: size_t,
    offset: off_t,
) -> ssize_t {
    Sys::pread(
        fildes,
        unsafe { slice::from_raw_parts_mut(buf.cast::<u8>(), nbyte) },
        offset,
    )
    .map(|read| read as ssize_t)
    .syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/pwrite.html>.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pwrite(
    fildes: c_int,
    buf: *const c_void,
    nbyte: size_t,
    offset: off_t,
) -> ssize_t {
    Sys::pwrite(
        fildes,
        unsafe { slice::from_raw_parts(buf.cast::<u8>(), nbyte) },
        offset,
    )
    .map(|written| written as ssize_t)
    .syscall_failed()
}

/// NOTE: blueos only has process 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getuid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn getuid() -> uid_t {
    0
}

/// NOTE: blueos only has user 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/geteuid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn geteuid() -> uid_t {
    0
}

/// NOTE: blueos only has process 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getgid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn getgid() -> gid_t {
    0
}

/// NOTE: blueos only has process 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getpid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn getpid() -> pid_t {
    0
}

/// NOTE: blueos only has process 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getppid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn getppid() -> pid_t {
    0
}

/// NOTE: blueos only has user 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/seteuid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn seteuid(_uid: uid_t) -> c_int {
    0
}

/// NOTE: blueos only has process 0
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/setsid.html>.
#[unsafe(no_mangle)]
pub extern "C" fn setsid() -> pid_t {
    0
}

#[unsafe(no_mangle)]
pub fn realpath(
    pathname: *const core::ffi::c_char,
    _resolved: *mut core::ffi::c_char,
) -> *mut core::ffi::c_char {
    pathname as *mut core::ffi::c_char
}
