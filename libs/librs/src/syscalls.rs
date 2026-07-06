// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

// Newlib syscall adapters. Newlib's reentrant wrappers (_read_r, _write_r,
// _fstat_r, _sbrk_r, etc.) call these underscore-prefixed interfaces.
// We route them through bk_syscall! to the kernel.
// _malloc_r, _free_r, and _realloc_r are routed to the BlueOS allocator
// from the linker report we should use _reent(maybe not) ??

use blueos_header::syscalls::NR::{
    ClockGetTime, ClockNanoSleep, Close, FStat, Lseek, Open, Read, SchedYield, Write,
};
use blueos_scal::bk_syscall;
use core::slice;
use libc::{c_int, c_void, clockid_t, off_t, size_t, ssize_t, timespec};

pub const CLOCK_REALTIME: clockid_t = 0;
pub const CLOCK_MONOTONIC: clockid_t = 1;

#[no_mangle]
pub unsafe extern "C" fn posix_memalign(
    ptr: *mut *mut c_void,
    align: size_t,
    size: size_t,
) -> c_int {
    let addr = blueos::allocator::malloc_align(size, align);
    if addr.is_null() {
        return -1;
    }
    unsafe { *ptr = addr as *mut c_void };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    blueos::allocator::free(ptr as *mut u8);
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _free_r(_reent: *mut c_void, ptr: *mut c_void) {
    blueos::allocator::free(ptr as *mut u8);
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _malloc_r(_reent: *mut c_void, size: size_t) -> *mut c_void {
    blueos::allocator::malloc(size) as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _calloc_r(
    _reent: *mut c_void,
    nmemb: size_t,
    size: size_t,
) -> *mut c_void {
    blueos::allocator::calloc(nmemb, size) as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _realloc_r(
    _reent: *mut c_void,
    ptr: *mut c_void,
    size: size_t,
) -> *mut c_void {
    blueos::allocator::realloc(ptr as *mut u8, size) as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    blueos::allocator::malloc(size) as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> c_int {
    bk_syscall!(ClockNanoSleep, CLOCK_MONOTONIC, 0, rqtp, rmtp) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _read(fd: c_int, buf: *mut c_void, len: size_t) -> ssize_t {
    if buf.is_null() {
        return -1;
    }
    let buf = slice::from_raw_parts_mut(buf as *mut u8, len);
    bk_syscall!(Read, fd, buf.as_mut_ptr() as *mut c_void, buf.len()) as ssize_t
}

#[no_mangle]
pub unsafe extern "C" fn _write(fd: c_int, buf: *const c_void, len: size_t) -> ssize_t {
    if buf.is_null() {
        return -1;
    }
    let buf = slice::from_raw_parts(buf as *const u8, len);
    bk_syscall!(Write, fd, buf.as_ptr(), buf.len()) as ssize_t
}

#[no_mangle]
pub unsafe extern "C" fn _open(path: *const u8, flags: c_int, mode: c_int) -> c_int {
    bk_syscall!(Open, path as *const i8, flags, mode.try_into().unwrap_or(0)) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _close(fd: c_int) -> c_int {
    bk_syscall!(Close, fd) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _lseek(fd: c_int, offset: off_t, whence: c_int) -> off_t {
    bk_syscall!(Lseek, fd, offset as usize, whence) as off_t
}

#[no_mangle]
pub unsafe extern "C" fn _fstat(fd: c_int, st: *mut c_void) -> c_int {
    bk_syscall!(FStat, fd, st as *mut i8) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _isatty(fd: c_int) -> c_int {
    (fd < 3) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _kill(_pid: c_int, _sig: c_int) -> c_int {
    -1
}

#[no_mangle]
pub extern "C" fn _getpid() -> c_int {
    // no processes
    0
}

const EPOCH_BASE_SECS: i64 = 1767225600; // 2026-01-01T00:00:00Z

#[no_mangle]
pub extern "C" fn gettimeofday(tp: *mut libc::timeval, tzp: *mut c_void) -> c_int {
    if !tp.is_null() {
        let mut ts = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        bk_syscall!(ClockGetTime, CLOCK_REALTIME, &mut ts as *mut libc::timespec);
        unsafe {
            (*tp).tv_sec = ts.tv_sec + 0 as libc::time_t;
            (*tp).tv_usec = ts.tv_nsec / 1000;
        }
    }
    0
}

#[no_mangle]
pub extern "C" fn _gettimeofday(tp: *mut libc::timeval, tzp: *mut c_void) -> c_int {
    gettimeofday(tp, tzp)
}

#[no_mangle]
pub unsafe extern "C" fn clock_gettime(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    bk_syscall!(ClockGetTime, clock_id, tp) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sched_yield() -> c_int {
    bk_syscall!(SchedYield) as c_int
}
