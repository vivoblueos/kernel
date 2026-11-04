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
//
// This file is the generic newlib adapter only. The QuickJS front-end POSIX
// surface (stat/chdir/poll/termios/ENOSYS stubs/nanosleep/...) lives in
// qjs_support.rs, which builds on the underscore stubs defined here.

use blueos_header::syscalls::NR::{
    ClockGetTime, Close, FStat, Lseek, Open, Read, SchedYield, Write,
};
use blueos_scal::bk_syscall;
use core::slice;
use libc::{c_int, c_void, clockid_t, off_t, size_t, ssize_t};

// The kernel's clock numbering. A C caller that names a clock (clock_gettime,
// clock_nanosleep, ...) passes newlib's numbering instead, so those entry
// points translate first - see c_clock_id.rs.
pub const CLOCK_REALTIME: clockid_t = crate::c_clock_id::KERNEL_REALTIME;
pub const CLOCK_MONOTONIC: clockid_t = crate::c_clock_id::KERNEL_MONOTONIC;

// _malloc_r/_calloc_r/_realloc_r are routed to the BlueOS allocator.
// Alignment contract: malloc must return storage aligned to at least
// _Alignof(max_align_t) == 8 bytes on this target. quickjs-ng hard-requires
// this — its JSMallocBlockHeader is `_Alignas(8)` and every GC/refcount field is
// read back at a fixed negative offset from the user pointer, and the NAN-boxed
// JSValue tagging (`JS_VALUE_GET_PTR(v) & ~15`) silently masks a 4-byte-
// misaligned object pointer while corrupting the embedded double/u64 payload.
// so allocate 8-aligned and assert it.
#[inline]
unsafe fn sys_alloc(size: size_t) -> *mut c_void {
    let p = blueos::allocator::malloc_align(size, 8);
    debug_assert!(p.is_null() || (p as usize) % 8 == 0);
    p as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _free_r(_reent: *mut c_void, ptr: *mut c_void) {
    blueos::allocator::free(ptr as *mut u8);
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _malloc_r(_reent: *mut c_void, size: size_t) -> *mut c_void {
    unsafe { sys_alloc(size) }
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _calloc_r(
    _reent: *mut c_void,
    nmemb: size_t,
    size: size_t,
) -> *mut c_void {
    let p = blueos::allocator::calloc(nmemb, size);
    debug_assert!(p.is_null() || (p as usize) % 8 == 0);
    p as *mut c_void
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn _realloc_r(
    _reent: *mut c_void,
    ptr: *mut c_void,
    size: size_t,
) -> *mut c_void {
    let p = blueos::allocator::realloc(ptr as *mut u8, size);
    debug_assert!(p.is_null() || (p as usize) % 8 == 0);
    p as *mut c_void
}

// _memalign_r backs memalign() and, through it, the Issue 8 aligned_alloc():
// newlib does not define _aligned_alloc_r, so aligned_alloc() reaches memalign().
// Without this, the linker pulls in newlib's own sbrk-based malloc
// (libc_a-mallocr.o) next to the BlueOS allocator already wired into
// _malloc_r. Two allocators over two heaps is worse than a missing symbol -
// a pointer taken from one and freed into the other corrupts the heap instead
// of failing - so every entry point in the family has to land in the same one.
#[inline]
unsafe fn sys_alloc_aligned(size: size_t, align: size_t) -> *mut c_void {
    // C requires a power-of-two alignment. 0 means "no constraint", which
    // still has to satisfy the max_align_t contract sys_alloc documents.
    if align == 0 {
        return sys_alloc(size);
    }
    if !align.is_power_of_two() {
        return core::ptr::null_mut();
    }
    let align = if align < 8 { 8 } else { align };
    let p = blueos::allocator::malloc_align(size, align);
    debug_assert!(p.is_null() || (p as usize) % align == 0);
    p as *mut c_void
}

// Strong, not weak, on purpose. newlib's libc.a defines _memalign_r inside the
// same object as its sbrk-based malloc, and a weak definition here loses to it:
// the linker then extracts that object to satisfy memalign() and pulls
// _sbrk_r -> _sbrk in with it. Worse, the two allocators would then be live at
// once over two different heaps. Taking the symbol strongly keeps every entry
// point in the BlueOS allocator.
#[no_mangle]
pub unsafe extern "C" fn _memalign_r(
    _reent: *mut c_void,
    align: size_t,
    size: size_t,
) -> *mut c_void {
    unsafe { sys_alloc_aligned(size, align) }
}

// Provided for a C library that calls it directly rather than going through
// memalign().
#[no_mangle]
pub unsafe extern "C" fn _aligned_alloc_r(
    _reent: *mut c_void,
    align: size_t,
    size: size_t,
) -> *mut c_void {
    unsafe { sys_alloc_aligned(size, align) }
}

// malloc_usable_size is a glibc/newlib extension. The Bellard QuickJS default
// allocator (js_def_*, quickjs.c) calls it unconditionally on non-Apple/
// non-Windows/non-glibc targets, Provided weak so a C library
// that does define it wins.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn malloc_usable_size(_ptr: *mut c_void) -> size_t {
    0
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
pub extern "C" fn sched_yield() -> c_int {
    bk_syscall!(SchedYield) as c_int
}
