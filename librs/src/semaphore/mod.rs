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

use core::ptr;
use libc::{c_char, c_int, c_uint};

use crate::time::deadline::{Deadline, C_CLOCK_REALTIME};

pub type RsSemaphore = crate::sync::semaphore::Semaphore;

/// The C library's `sem_t`.
///
/// The `libc` crate describes the Linux type, which is a 16/32-byte union
/// reserved for the futex-based Linux implementation. This kernel's
/// semaphore is a single counter, so the type has to be sized to match
/// [`RsSemaphore`] - otherwise a C caller would hand the kernel a pointer
/// to an object that is four times too large, and the cast in
/// `sem_init()` would write past the end of the caller's object.
///
/// The layout is pinned by the `check_size!` assertion in
/// `librs/src/pthread.rs` and by the matching `_Static_assert` in
/// `librs/include/semaphore.h`.
#[allow(non_camel_case_types)]
pub type sem_t = RsSemaphore;

#[no_mangle]
pub unsafe extern "C" fn sem_close(sem: *mut sem_t) -> c_int {
    ptr::drop_in_place(sem.cast::<RsSemaphore>());
    0
}

#[no_mangle]
pub unsafe extern "C" fn sem_destroy(sem: *mut sem_t) -> c_int {
    ptr::drop_in_place(sem.cast::<RsSemaphore>());
    0
}

#[no_mangle]
pub unsafe extern "C" fn sem_getvalue(sem: *mut sem_t, sval: *mut c_int) -> c_int {
    sval.write(get(sem).value() as c_int);

    0
}

#[no_mangle]
pub unsafe extern "C" fn sem_init(sem: *mut sem_t, _pshared: c_int, value: c_uint) -> c_int {
    sem.cast::<RsSemaphore>()
        .write(RsSemaphore::new(value as usize));

    0
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sem_open.html>.
// TODO: va_list
// #[no_mangle]
pub unsafe extern "C" fn sem_open(
    _name: *const c_char,
    _oflag: c_int, /* (va_list) value: c_uint */
) -> *mut sem_t {
    todo!("named semaphores")
}

#[no_mangle]
pub unsafe extern "C" fn sem_post(sem: *mut sem_t) -> c_int {
    get(sem).post(1);

    0
}

#[no_mangle]
pub unsafe extern "C" fn sem_trywait(sem: *mut sem_t) -> c_int {
    if get(sem).try_wait() {
        0
    } else {
        // POSIX requires EAGAIN when the semaphore is not available.
        crate::errno::ERRNO.set(libc::EAGAIN);
        -1
    }
}

#[no_mangle]
pub unsafe extern "C" fn sem_unlink(_name: *const c_char) -> c_int {
    todo!("named semaphores")
}

#[no_mangle]
pub unsafe extern "C" fn sem_wait(sem: *mut sem_t) -> c_int {
    get(sem).wait(None);

    0
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sem_timedwait.html>.
///
/// `abs_timeout` is an absolute deadline on `CLOCK_REALTIME`.
#[no_mangle]
pub unsafe extern "C" fn sem_timedwait(
    sem: *mut sem_t,
    abs_timeout: *const libc::timespec,
) -> c_int {
    sem_clockwait(sem, C_CLOCK_REALTIME, abs_timeout)
}

/// Issue 8 `sem_clockwait`: waits on `sem` until it can be acquired or the
/// absolute deadline `abs_timeout` on `clock_id` passes.
///
/// Unlike `sem_timedwait`, the deadline may be expressed on any clock the
/// kernel implements, which lets a caller wait on `CLOCK_MONOTONIC` and be
/// immune to wall-clock adjustments.
#[no_mangle]
pub unsafe extern "C" fn sem_clockwait(
    sem: *mut sem_t,
    clock_id: libc::clockid_t,
    abs_timeout: *const libc::timespec,
) -> c_int {
    if abs_timeout.is_null() {
        crate::errno::ERRNO.set(libc::EINVAL);
        return -1;
    }
    // POSIX distinguishes "this clock does not exist" (EINVAL) from "the
    // deadline has passed" (ETIMEDOUT).
    if crate::time::deadline::validate_clock(clock_id) != 0 {
        crate::errno::ERRNO.set(libc::EINVAL);
        return -1;
    }
    let abs_timeout = &*abs_timeout;
    if crate::time::deadline::validate_timespec(abs_timeout) != 0 {
        crate::errno::ERRNO.set(libc::EINVAL);
        return -1;
    }

    let deadline = Deadline::new(clock_id, *abs_timeout);
    if deadline.remaining().is_none() {
        // The deadline has already passed. POSIX still allows the wait to
        // succeed if the semaphore happens to be available.
        if get(sem).try_wait() {
            return 0;
        }
        crate::errno::ERRNO.set(libc::ETIMEDOUT);
        return -1;
    }

    if get(sem).wait_until(&deadline) {
        0
    } else {
        crate::errno::ERRNO.set(libc::ETIMEDOUT);
        -1
    }
}

unsafe fn get<'any>(sem: *mut sem_t) -> &'any RsSemaphore {
    &*sem.cast()
}
