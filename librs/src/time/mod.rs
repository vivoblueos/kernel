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

use crate::errno::ERRNO;
use blueos_header::syscalls::NR::{
    ClockGetTime, ClockNanoSleep, ClockSetTime, TimerCreate, TimerDelete, TimerGetOverrun,
    TimerGetTime, TimerSetTime,
};
use blueos_scal::bk_syscall;
use core::{arch::asm, mem};
use libc::{
    c_double, c_int, c_long, c_uint, c_void, clock_t, clockid_t, itimerspec, sigevent, time_t,
    timer_t, timespec, EINVAL,
};

const NANOSECONDS_PER_SECOND: u64 = 1_000_000_000;

// assume ns resolution for all clocks, kernel will convert it
const CLOCK_RESOLUTION_NS: c_long = 1;

#[inline]
const fn is_supported_clock(clock_id: clockid_t) -> bool {
    matches!(
        clock_id,
        CLOCK_REALTIME | CLOCK_MONOTONIC | CLOCK_PROCESS_CPUTIME_ID | CLOCK_THREAD_CPUTIME_ID
    )
}

// POSIX required REALTIME and MONOTONIC clocks, currently, we treat PROCESS_CPUTIME_ID and THREAD_CPUTIME_ID
// same, it maybe affect clock_nanosleep behavior in some cases.
//
// These are the *kernel's* ids. A C caller passes newlib's ids instead, so
// every `extern "C"` clock entry point translates with `c_clock_id::from_c`
// before issuing the syscall - see c_clock_id.rs for the two tables.
mod c_clock_id;

pub mod deadline;

pub use c_clock_id::{
    KERNEL_MONOTONIC as CLOCK_MONOTONIC, KERNEL_PROCESS_CPUTIME_ID as CLOCK_PROCESS_CPUTIME_ID,
    KERNEL_REALTIME as CLOCK_REALTIME, KERNEL_THREAD_CPUTIME_ID as CLOCK_THREAD_CPUTIME_ID,
};

pub const CLOCKS_PER_SEC: c_long = 1_000_000;

/// `clock_gettime` in the kernel's clock numbering.
///
/// Rust callers inside librs use this directly; the exported `clock_gettime`
/// wraps it after translating the id it got from C.
pub fn clock_gettime_in_kernel_ids(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    let ret = unsafe { bk_syscall!(ClockGetTime, clock_id, tp) as isize };
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

#[no_mangle]
pub unsafe extern "C" fn clock_gettime(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    let Some(kernel_id) = c_clock_id::from_c(clock_id) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    clock_gettime_in_kernel_ids(kernel_id, tp)
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/time.html>
#[no_mangle]
pub unsafe extern "C" fn time(tloc: *mut time_t) -> time_t {
    let mut ts = timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    if clock_gettime_in_kernel_ids(CLOCK_REALTIME, &mut ts as *mut timespec) != 0 {
        return -1;
    }
    if !tloc.is_null() {
        *tloc = ts.tv_sec
    };
    ts.tv_sec
}

/// Issue 8 `timespec_get`: stores the current time of `base` in `ts`.
///
/// `base` is a `clockid_t` naming the clock to read. On success the function
/// returns `base` itself, which lets a caller chain the call; on failure it
/// returns -1 and sets `errno` to `EINVAL`.
///
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timespec_get.html>
#[no_mangle]
pub unsafe extern "C" fn timespec_get(ts: *mut timespec, base: clockid_t) -> c_int {
    if ts.is_null() {
        ERRNO.set(EINVAL);
        return -1;
    }
    let Some(kernel_id) = c_clock_id::from_c(base) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    if !is_supported_clock(kernel_id) {
        ERRNO.set(EINVAL);
        return -1;
    }
    if clock_gettime_in_kernel_ids(kernel_id, ts) != 0 {
        return -1;
    }
    base as c_int
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_getres.html>.
#[no_mangle]
pub unsafe extern "C" fn clock_getres(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    let Some(clock_id) = c_clock_id::from_c(clock_id) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    if !is_supported_clock(clock_id) {
        ERRNO.set(EINVAL);
        return -1;
    }
    if tp.is_null() {
        return 0;
    }
    *tp = timespec {
        tv_sec: 0,
        tv_nsec: CLOCK_RESOLUTION_NS,
    };
    0
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_getres.html>.
#[no_mangle]
pub unsafe extern "C" fn clock_settime(clock_id: clockid_t, tp: *const timespec) -> c_int {
    // we havn't support wall clock source or rtc, now , it's an workaround, when user setting
    // CLOCK_REALTIME, we get the real system time, then the realtime offset to monotonic time
    let Some(clock_id) = c_clock_id::from_c(clock_id) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    let ret = bk_syscall!(ClockSetTime, clock_id, tp) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_nanosleep.html>.
#[no_mangle]
pub unsafe extern "C" fn clock_nanosleep(
    clock_id: clockid_t,
    flags: c_int,
    rqtp: *const timespec,
    rmtp: *mut timespec,
) -> c_int {
    let Some(clock_id) = c_clock_id::from_c(clock_id) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    let ret = bk_syscall!(ClockNanoSleep, clock_id, flags, rqtp, rmtp) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/nanosleep.html>.
#[no_mangle]
pub unsafe extern "C" fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> c_int {
    let ret = bk_syscall!(ClockNanoSleep, CLOCK_MONOTONIC, 0, rqtp, rmtp) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock.html>.
#[no_mangle]
pub extern "C" fn clock() -> clock_t {
    let mut ts = mem::MaybeUninit::<timespec>::uninit();

    if clock_gettime_in_kernel_ids(CLOCK_PROCESS_CPUTIME_ID, ts.as_mut_ptr()) != 0 {
        return -1;
    }
    let ts = unsafe { ts.assume_init() };

    let clocks = ts.tv_sec as i64 * CLOCKS_PER_SEC as i64
        + ts.tv_nsec as i64 / (1_000_000_000_i64 / CLOCKS_PER_SEC as i64);
    clock_t::try_from(clocks).unwrap_or(-1)
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/difftime.html>.
#[no_mangle]
pub extern "C" fn difftime(time1: time_t, time0: time_t) -> c_double {
    (time1 - time0) as c_double
}

#[no_mangle]
pub extern "C" fn usleep(usec: c_uint) -> c_int {
    let rqtp = timespec {
        tv_sec: (usec / 1_000_000) as time_t,
        tv_nsec: ((usec % 1_000_000) * 1000) as c_long,
    };
    let rmtp = core::ptr::null_mut();
    unsafe { nanosleep(&rqtp, rmtp) }
}

#[no_mangle]
pub extern "C" fn msleep(msec: c_uint) -> c_int {
    let rqtp = timespec {
        tv_sec: (msec / 1000) as time_t,
        tv_nsec: ((msec % 1000) * 1_000_000) as c_long,
    };
    let rmtp = core::ptr::null_mut();
    unsafe { nanosleep(&rqtp, rmtp) }
}

#[no_mangle]
pub extern "C" fn ssleep(sec: c_uint) -> c_int {
    let rqtp = timespec {
        tv_sec: sec as time_t,
        tv_nsec: 0,
    };
    let rmtp = core::ptr::null_mut();
    unsafe { nanosleep(&rqtp, rmtp) }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timer_create.html>.
#[no_mangle]
pub unsafe extern "C" fn timer_create(
    clock_id: clockid_t,
    evp: *mut sigevent,
    timerid: *mut timer_t,
) -> c_int {
    let Some(clock_id) = c_clock_id::from_c(clock_id) else {
        ERRNO.set(EINVAL);
        return -1;
    };
    let ret = bk_syscall!(TimerCreate, clock_id, evp, timerid) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timer_delete.html>.
#[no_mangle]
pub unsafe extern "C" fn timer_delete(timerid: timer_t) -> c_int {
    let ret = bk_syscall!(TimerDelete, timerid) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timer_getoverrun.html>.
#[no_mangle]
pub unsafe extern "C" fn timer_getoverrun(timerid: timer_t) -> c_int {
    let ret = bk_syscall!(TimerGetOverrun, timerid) as isize;
    if ret >= 0 {
        ret as c_int
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timer_gettime.html>.
#[no_mangle]
pub unsafe extern "C" fn timer_gettime(timerid: timer_t, value: *mut itimerspec) -> c_int {
    let ret = bk_syscall!(TimerGetTime, timerid, value) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/timer_settime.html>.
#[no_mangle]
pub unsafe extern "C" fn timer_settime(
    timerid: timer_t,
    flags: c_int,
    value: *const itimerspec,
    ovalue: *mut itimerspec,
) -> c_int {
    let ret = bk_syscall!(TimerSetTime, timerid, flags, value, ovalue) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// not defined in POSIX, but used in some implementations
#[cfg(target_arch = "arm")]
#[no_mangle]
pub extern "C" fn udelay(usec: c_uint) {
    const CYCLES_PER_USEC: u32 = 1_00; // not exact, this value should get from kernel
    let cycles = usec * CYCLES_PER_USEC;
    unsafe {
        busy_wait(cycles);
    }
}

#[cfg(target_arch = "arm")]
#[inline(always)]
#[allow(clippy::while_immutable_condition)]
unsafe fn busy_wait(cycles: u32) {
    let count = cycles;
    while count > 0 {
        asm!(
            "subs {0}, {0}, #1",
            inout(reg) count => _,
            options(nomem, nostack, preserves_flags)
        );
    }
}

#[cfg(target_arch = "arm")]
#[no_mangle]
pub extern "C" fn mdelay(msec: c_uint) {
    const CYCLES_PER_MSEC: u32 = 100_000; // not exact, this value should get from kernel
    let cycles = msec * CYCLES_PER_MSEC;
    unsafe {
        busy_wait(cycles);
    }
}

#[cfg(target_arch = "arm")]
#[no_mangle]
pub extern "C" fn ndelay(nsec: c_uint) {
    udelay(nsec / 1000); // convert nanoseconds to microseconds
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    // The exported entry points take the C library's numbering, so the tests
    // below must pass newlib ids, not the kernel ones re-exported by `super`.
    // Shadowing the glob import is what keeps every call site below honest.
    use super::c_clock_id::{
        C_CLOCK_MONOTONIC as CLOCK_MONOTONIC, C_CLOCK_REALTIME as CLOCK_REALTIME,
    };

    fn ts_to_ns(ts: &timespec) -> i128 {
        // Convert timespec to total nanoseconds as i128 to avoid overflow.
        (ts.tv_sec as i128) * (NANOSECONDS_PER_SECOND as i128) + (ts.tv_nsec as i128)
    }

    fn assert_ts_close(actual: &timespec, expected: &timespec, tolerance_ns: i128) {
        let delta = ts_to_ns(actual) - ts_to_ns(expected);
        let delta = if delta < 0 { -delta } else { delta };
        assert!(
            delta <= tolerance_ns,
            "timespec mismatch: delta_ns={} tol_ns={}",
            delta,
            tolerance_ns
        );
    }

    fn assert_elapsed_at_least(before: &timespec, after: &timespec, min_ns: i128) {
        let elapsed = ts_to_ns(after) - ts_to_ns(before);
        assert!(
            elapsed >= min_ns,
            "elapsed too small: elapsed_ns={} min_ns={}",
            elapsed,
            min_ns
        );
    }

    #[test]
    fn check_clock_realtime_and_time() {
        let epoch = timespec {
            tv_sec: 1_700_000_000,
            tv_nsec: 123_456_789,
        };
        unsafe {
            assert_eq!(clock_settime(CLOCK_REALTIME, &epoch as *const timespec), 0);

            let mut got = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            assert_eq!(clock_gettime(CLOCK_REALTIME, &mut got as *mut timespec), 0);
            // The clock is tick based, and under QEMU/TCG a tick can be several
            // milliseconds late when the host is loaded, so the tolerance has to
            // cover more than the nominal tick period (100Hz here) rather than
            // just one or two ticks.
            assert_ts_close(&got, &epoch, 100_000_000); // 100ms
            let sec = time(core::ptr::null_mut());
            assert!(sec >= epoch.tv_sec);
            assert!(sec <= epoch.tv_sec + 1);
        }
    }

    #[test]
    fn check_monotonic_time() {
        unsafe {
            let mut before = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            let mut after = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut before as *mut timespec),
                0
            );
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut after as *mut timespec),
                0
            );
            assert!(ts_to_ns(&after) >= ts_to_ns(&before));
        }

        let c1 = clock();
        let c2 = clock();
        assert!(c1 >= 0);
        assert!(c2 >= 0);
        assert!(c2 >= c1);
    }

    #[test]
    fn check_monotonic_nanosleep() {
        let req = timespec {
            tv_sec: 0,
            tv_nsec: 20_000_000, // 20ms
        };
        unsafe {
            let mut before = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            let mut after = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut before as *mut timespec),
                0
            );
            assert_eq!(nanosleep(&req as *const timespec, core::ptr::null_mut()), 0);
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut after as *mut timespec),
                0
            );
            // tick based approximation +/- 1 ticks
            assert_elapsed_at_least(&before, &after, 10_000_000 as i128);
        }
    }

    #[test]
    fn check_monotonic_clock_nanosleep() {
        let req = timespec {
            tv_sec: 0,
            tv_nsec: 20_000_000, // 20ms
        };
        unsafe {
            let mut before = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            let mut after = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut before as *mut timespec),
                0
            );
            assert_eq!(
                clock_nanosleep(
                    CLOCK_MONOTONIC,
                    0,
                    &req as *const timespec,
                    core::ptr::null_mut()
                ),
                0
            );
            assert_eq!(
                clock_gettime(CLOCK_MONOTONIC, &mut after as *mut timespec),
                0
            );
            // tick based clock appromation +/- 1 ticks
            assert_elapsed_at_least(&before, &after, 10_000_000 as i128);
        }
    }

    // Regression test for the id mismatch: newlib numbers CLOCK_REALTIME 1 and
    // CLOCK_MONOTONIC 4 while the kernel uses 0 and 1. Before the translation
    // `clock_gettime(CLOCK_REALTIME)` read the monotonic clock (tv_sec 0,
    // tv_nsec negative once the tick had not yet accumulated) and
    // `clock_gettime(CLOCK_MONOTONIC)` failed with EINVAL.
    #[test]
    fn check_clock_id_translation() {
        for c_id in [
            c_clock_id::C_CLOCK_REALTIME,
            c_clock_id::C_CLOCK_MONOTONIC,
            c_clock_id::C_CLOCK_PROCESS_CPUTIME_ID,
            c_clock_id::C_CLOCK_THREAD_CPUTIME_ID,
        ] {
            let mut ts = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            assert_eq!(unsafe { clock_gettime(c_id, &mut ts as *mut timespec) }, 0);
            assert!(
                ts.tv_nsec >= 0 && (ts.tv_nsec as u64) < NANOSECONDS_PER_SECOND,
                "c clock id {} produced tv_nsec={}",
                c_id,
                ts.tv_nsec
            );
        }

        // The kernel's own ids are not part of the C ABI; a C caller cannot
        // produce them, and accepting them would alias CLOCK_REALTIME(0) onto
        // nothing at all while aliasing 1 onto the monotonic clock.
        let mut ts = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        assert_eq!(
            unsafe { clock_gettime(c_clock_id::KERNEL_REALTIME, &mut ts as *mut timespec) },
            -1
        );
        assert_eq!(ERRNO.get(), EINVAL);
    }
}
