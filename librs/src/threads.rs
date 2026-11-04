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

//! C11 `<threads.h>` (POSIX.1-2024, Issue 8 requires all 25 interfaces).
//!
//! The bundled newlib ships a `<threads.h>` whose `machine/_threads.h` does
//! not exist, and its libc.a contains none of the `thrd_*` / `mtx_*` / `cnd_*`
//! / `tss_*` / `call_once` symbols. We provide the header ourselves
//! (`librs/include/threads.h`) and implement everything here in Rust.
//!
//! IMPORTANT ABI NOTE: newlib's C `pthread_mutex_t` / `pthread_cond_t` are
//! single 32-bit ids, far too narrow to hold the Rust `Mutex` / `Cond`
//! objects the pthread layer stores in them. `mtx_t` and `cnd_t` therefore
//! get their own opaque, properly sized storage in the header, and the
//! static asserts below pin both sides to the same layout. The pthread
//! layer's type mismatch for C callers is a separate pre-existing issue.

use crate::sync::cond::Cond;
use crate::sync::mutex::{Mutex, MutexAttr};
use crate::pthread::{
    pthread_create, pthread_detach, pthread_exit, pthread_join, pthread_key_create,
    pthread_key_delete, pthread_getspecific, pthread_self, pthread_setspecific, pthread_t,
};
use crate::sched::sched_yield;
use crate::time::{clock_gettime, nanosleep};
use alloc::boxed::Box;
use core::ffi::{c_int, c_void};
use core::ptr;
use core::sync::atomic::{AtomicU32, Ordering};
use libc::{clockid_t, pthread_key_t, timespec, CLOCK_REALTIME, PTHREAD_MUTEX_RECURSIVE, ETIMEDOUT, ENOMEM};

// Pin the C header's opaque storage to the Rust objects. If either side
// changes, this fails the build instead of corrupting a C caller's stack.
// Sizes depend on the pointer width: Mutex is two AtomicUsize + Ty + bool
// (24 bytes, 8-aligned on 64-bit; 12 bytes, 4-aligned on 32-bit), Cond is
// two AtomicUsize plus the clock its deadlines are measured on, with an
// explicit 8-byte alignment on both.
const _: () = {
    #[cfg(target_pointer_width = "64")]
    {
        assert!(core::mem::size_of::<Mutex>() == 24, "mtx_t layout drifted");
        assert!(core::mem::align_of::<Mutex>() == 8, "mtx_t alignment drifted");
        assert!(core::mem::size_of::<Cond>() == 24, "cnd_t layout drifted");
        assert!(core::mem::align_of::<Cond>() == 8, "cnd_t alignment drifted");
    }
    #[cfg(target_pointer_width = "32")]
    {
        assert!(core::mem::size_of::<Mutex>() == 12, "mtx_t layout drifted");
        assert!(core::mem::align_of::<Mutex>() == 4, "mtx_t alignment drifted");
        assert!(core::mem::size_of::<Cond>() == 16, "cnd_t layout drifted");
        assert!(core::mem::align_of::<Cond>() == 8, "cnd_t alignment drifted");
    }
};

// Values from the C11 standard; keep in sync with librs/include/threads.h.
pub const THRD_SUCCESS: c_int = 4;
pub const THRD_NOMEM: c_int = 3;
pub const THRD_BUSY: c_int = 1;
pub const THRD_ERROR: c_int = 2;
pub const THRD_TIMEDOUT: c_int = 5;

// Bit flags from C11; keep in sync with the header.
pub const MTX_PLAIN: c_int = 0x1;
pub const MTX_RECURSIVE: c_int = 0x2;
pub const MTX_TIMED: c_int = 0x4;

type ThrdStart = extern "C" fn(arg: *mut c_void) -> c_int;

fn map(err: c_int) -> c_int {
    match err {
        0 => THRD_SUCCESS,
        e if e == libc::EBUSY => THRD_BUSY,
        e if e == ETIMEDOUT => THRD_TIMEDOUT,
        e if e == ENOMEM => THRD_NOMEM,
        _ => THRD_ERROR,
    }
}

fn now(clock: clockid_t) -> timespec {
    let mut ts = timespec { tv_sec: 0, tv_nsec: 0 };
    unsafe { clock_gettime(clock, &mut ts) };
    ts
}

fn ts_ge(a: &timespec, b: &timespec) -> bool {
    (a.tv_sec, a.tv_nsec) >= (b.tv_sec, b.tv_nsec)
}

// ---------------------------------------------------------------------------
// thrd_*
// ---------------------------------------------------------------------------

struct ThrdArgs {
    start: ThrdStart,
    arg: *mut c_void,
}

extern "C" fn thrd_trampoline(arg: *mut c_void) -> *mut c_void {
    let args = unsafe { Box::from_raw(arg as *mut ThrdArgs) };
    let res = (args.start)(args.arg);
    // A C11 thread exits with `int`; smuggle it through the `void*` return
    // the same way pthread_exit does.
    res as isize as *mut c_void
}

/// C11 `thrd_create`.
#[no_mangle]
pub unsafe extern "C" fn thrd_create(
    thr: *mut pthread_t,
    func: ThrdStart,
    arg: *mut c_void,
) -> c_int {
    if thr.is_null() {
        return THRD_ERROR;
    }
    let boxed = Box::new(ThrdArgs { start: func, arg });
    let err = pthread_create(
        thr,
        ptr::null(),
        thrd_trampoline,
        Box::into_raw(boxed) as *mut c_void,
    );
    if err == 0 {
        THRD_SUCCESS
    } else {
        THRD_ERROR
    }
}

/// C11 `thrd_equal`.
#[no_mangle]
pub extern "C" fn thrd_equal(lhs: pthread_t, rhs: pthread_t) -> c_int {
    (lhs == rhs) as c_int
}

/// C11 `thrd_current`.
#[no_mangle]
pub extern "C" fn thrd_current() -> pthread_t {
    pthread_self()
}

/// C11 `thrd_exit`.
#[no_mangle]
pub unsafe extern "C" fn thrd_exit(res: c_int) -> ! {
    pthread_exit(res as isize as *mut c_void)
}

/// C11 `thrd_join`.
#[no_mangle]
pub unsafe extern "C" fn thrd_join(thr: pthread_t, res: *mut c_int) -> c_int {
    let mut retval: *mut c_void = ptr::null_mut();
    if pthread_join(thr, &mut retval) != 0 {
        return THRD_ERROR;
    }
    if !res.is_null() {
        *res = retval as isize as c_int;
    }
    THRD_SUCCESS
}

/// C11 `thrd_detach`.
#[no_mangle]
pub unsafe extern "C" fn thrd_detach(thr: pthread_t) -> c_int {
    map(pthread_detach(thr))
}

/// C11 `thrd_sleep`: 0 on success, -1 if interrupted, -2 on failure.
#[no_mangle]
pub unsafe extern "C" fn thrd_sleep(
    duration: *const timespec,
    remaining: *mut timespec,
) -> c_int {
    if duration.is_null() {
        return -2;
    }
    if nanosleep(duration, remaining) == 0 {
        0
    } else if crate::errno::ERRNO.get() == libc::EINTR {
        -1
    } else {
        -2
    }
}

/// C11 `thrd_yield`.
#[no_mangle]
pub unsafe extern "C" fn thrd_yield() {
    sched_yield();
}

// ---------------------------------------------------------------------------
// mtx_*
// ---------------------------------------------------------------------------

fn make_mutex_attr(ty: c_int) -> MutexAttr {
    let mut attr = MutexAttr::default();
    if ty & MTX_RECURSIVE != 0 {
        attr.ty = PTHREAD_MUTEX_RECURSIVE;
    }
    attr
}

/// C11 `mtx_init`.
#[no_mangle]
pub unsafe extern "C" fn mtx_init(mtx: *mut Mutex, ty: c_int) -> c_int {
    if mtx.is_null() || ty & !(MTX_PLAIN | MTX_RECURSIVE | MTX_TIMED) != 0 || ty == 0 {
        return THRD_ERROR;
    }
    match Mutex::new(&make_mutex_attr(ty)) {
        Ok(m) => {
            mtx.write(m);
            THRD_SUCCESS
        }
        Err(_) => THRD_ERROR,
    }
}

/// C11 `mtx_lock`.
#[no_mangle]
pub unsafe extern "C" fn mtx_lock(mtx: *mut Mutex) -> c_int {
    if mtx.is_null() {
        return THRD_ERROR;
    }
    match (*mtx).lock() {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `mtx_trylock`.
#[no_mangle]
pub unsafe extern "C" fn mtx_trylock(mtx: *mut Mutex) -> c_int {
    if mtx.is_null() {
        return THRD_ERROR;
    }
    match (*mtx).try_lock() {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `mtx_unlock`.
#[no_mangle]
pub unsafe extern "C" fn mtx_unlock(mtx: *mut Mutex) -> c_int {
    if mtx.is_null() {
        return THRD_ERROR;
    }
    match (*mtx).unlock() {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `mtx_destroy`.
#[no_mangle]
pub unsafe extern "C" fn mtx_destroy(mtx: *mut Mutex) {
    if !mtx.is_null() {
        ptr::drop_in_place(mtx);
    }
}

/// C11 `mtx_timedlock`: absolute CLOCK_REALTIME deadline. POSIX.1-2024
/// requires it for `mtx_timed` mutexes.
///
/// The kernel mutex primitive has no timed variant yet, so poll trylock with
/// a short sleep until the deadline.
#[no_mangle]
pub unsafe extern "C" fn mtx_timedlock(mtx: *mut Mutex, ts: *const timespec) -> c_int {
    if mtx.is_null() || ts.is_null() {
        return THRD_ERROR;
    }
    let deadline = *ts;
    let nap = timespec { tv_sec: 0, tv_nsec: 200_000 };
    loop {
        match (*mtx).try_lock() {
            Ok(()) => return THRD_SUCCESS,
            Err(libc::EBUSY) => {}
            Err(e) => return map(e),
        }
        if ts_ge(&now(CLOCK_REALTIME), &deadline) {
            return THRD_TIMEDOUT;
        }
        nanosleep(&nap, ptr::null_mut());
    }
}

// ---------------------------------------------------------------------------
// cnd_*
// ---------------------------------------------------------------------------

/// C11 `cnd_init`.
#[no_mangle]
pub unsafe extern "C" fn cnd_init(cnd: *mut Cond) -> c_int {
    if cnd.is_null() {
        return THRD_ERROR;
    }
    cnd.write(Cond::new());
    THRD_SUCCESS
}

/// C11 `cnd_signal`.
#[no_mangle]
pub unsafe extern "C" fn cnd_signal(cnd: *mut Cond) -> c_int {
    if cnd.is_null() {
        return THRD_ERROR;
    }
    match (*cnd).signal() {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `cnd_broadcast`.
#[no_mangle]
pub unsafe extern "C" fn cnd_broadcast(cnd: *mut Cond) -> c_int {
    if cnd.is_null() {
        return THRD_ERROR;
    }
    match (*cnd).broadcast() {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `cnd_wait`.
#[no_mangle]
pub unsafe extern "C" fn cnd_wait(cnd: *mut Cond, mtx: *mut Mutex) -> c_int {
    if cnd.is_null() || mtx.is_null() {
        return THRD_ERROR;
    }
    match (*cnd).wait(&*mtx) {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `cnd_timedwait`: absolute CLOCK_REALTIME deadline.
#[no_mangle]
pub unsafe extern "C" fn cnd_timedwait(
    cnd: *mut Cond,
    mtx: *mut Mutex,
    ts: *const timespec,
) -> c_int {
    if cnd.is_null() || mtx.is_null() || ts.is_null() {
        return THRD_ERROR;
    }
    // C11 specifies CLOCK_REALTIME for cnd_timedwait. The clock id is the C
    // library's, not the kernel's - see time/c_clock_id.rs.
    let deadline = crate::time::deadline::Deadline::new(
        crate::time::deadline::C_CLOCK_REALTIME,
        *ts,
    );
    match (*cnd).timedwait(&*mtx, &deadline) {
        Ok(()) => THRD_SUCCESS,
        Err(e) => map(e),
    }
}

/// C11 `cnd_destroy`.
#[no_mangle]
pub unsafe extern "C" fn cnd_destroy(cnd: *mut Cond) {
    if !cnd.is_null() {
        ptr::drop_in_place(cnd);
    }
}

// ---------------------------------------------------------------------------
// tss_* (thread-specific storage)
// ---------------------------------------------------------------------------

type TssDtor = Option<extern "C" fn(_: *mut c_void)>;

/// C11 `tss_create`.
#[no_mangle]
pub unsafe extern "C" fn tss_create(key: *mut pthread_key_t, dtor: TssDtor) -> c_int {
    if key.is_null() {
        return THRD_ERROR;
    }
    map(pthread_key_create(key, dtor))
}

/// C11 `tss_get`.
#[no_mangle]
pub unsafe extern "C" fn tss_get(key: pthread_key_t) -> *mut c_void {
    pthread_getspecific(key)
}

/// C11 `tss_set`.
#[no_mangle]
pub unsafe extern "C" fn tss_set(key: pthread_key_t, val: *mut c_void) -> c_int {
    map(pthread_setspecific(key, val))
}

/// C11 `tss_delete`.
#[no_mangle]
pub unsafe extern "C" fn tss_delete(key: pthread_key_t) {
    pthread_key_delete(key);
}

// ---------------------------------------------------------------------------
// call_once
// ---------------------------------------------------------------------------

// once_flag states.
const ONCE_IDLE: u32 = 0;
const ONCE_RUNNING: u32 = 1;
const ONCE_DONE: u32 = 2;

/// C11 `call_once`. `flag` starts zeroed; the first caller moves it
/// IDLE -> RUNNING and runs `init`, every other caller waits until DONE.
#[no_mangle]
pub unsafe extern "C" fn call_once(flag: *mut u32, init: extern "C" fn()) {
    if flag.is_null() {
        return;
    }
    let f = &*(flag as *const AtomicU32);
    if f.load(Ordering::Acquire) == ONCE_DONE {
        return;
    }
    if f
        .compare_exchange(ONCE_IDLE, ONCE_RUNNING, Ordering::Acquire, Ordering::Acquire)
        .is_ok()
    {
        init();
        f.store(ONCE_DONE, Ordering::Release);
        return;
    }
    // Someone else is running it: wait for DONE. A plain spin would burn CPU
    // and starve the runner on a single core, so nap between loads.
    let nap = timespec { tv_sec: 0, tv_nsec: 100_000 };
    while f.load(Ordering::Acquire) != ONCE_DONE {
        nanosleep(&nap, ptr::null_mut());
    }
}
