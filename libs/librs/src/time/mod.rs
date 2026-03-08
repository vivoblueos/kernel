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
pub const CLOCK_REALTIME: clockid_t = 0;
pub const CLOCK_MONOTONIC: clockid_t = 1;
pub const CLOCK_PROCESS_CPUTIME_ID: clockid_t = 2;
pub const CLOCK_THREAD_CPUTIME_ID: clockid_t = 3;

pub const CLOCKS_PER_SEC: c_long = 1_000_000;

#[no_mangle]
pub unsafe extern "C" fn clock_gettime(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    let ret = bk_syscall!(ClockGetTime, clock_id, tp) as isize;
    if ret >= 0 {
        0
    } else {
        ERRNO.set((-ret) as c_int);
        -1
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/time.html>
#[no_mangle]
pub unsafe extern "C" fn time(tloc: *mut time_t) -> time_t {
    let mut ts = timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    if clock_gettime(CLOCK_REALTIME, &mut ts as *mut timespec) != 0 {
        return -1;
    }
    if !tloc.is_null() {
        *tloc = ts.tv_sec
    };
    ts.tv_sec
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/clock_getres.html>.
#[no_mangle]
pub unsafe extern "C" fn clock_getres(clock_id: clockid_t, tp: *mut timespec) -> c_int {
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

    if unsafe { clock_gettime(CLOCK_PROCESS_CPUTIME_ID, ts.as_mut_ptr()) } != 0 {
        return -1;
    }
    let ts = unsafe { ts.assume_init() };

    let clocks = ts.tv_sec * CLOCKS_PER_SEC + (ts.tv_nsec / (1_000_000_000 / CLOCKS_PER_SEC));
    match clock_t::try_from(clocks) {
        Ok(ok) => ok,
        Err(_err) => -1,
    }
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
        tv_nsec: ((usec % 1_000_000) * 1000) as c_int,
    };
    let rmtp = core::ptr::null_mut();
    unsafe { nanosleep(&rqtp, rmtp) }
}

#[no_mangle]
pub extern "C" fn msleep(msec: c_uint) -> c_int {
    let rqtp = timespec {
        tv_sec: (msec / 1000) as time_t,
        tv_nsec: ((msec % 1000) * 1_000_000) as c_int,
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
            // tick based approximation +/- 1 ticks
            assert_ts_close(&got, &epoch, 20_000_000); // 20ms
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
}
