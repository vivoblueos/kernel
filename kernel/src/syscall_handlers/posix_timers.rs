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

// TODO: We should reuse the kernel timer and systick, and process signals in thread context.
// For now, keep minimal syscall stubs that preserve ABI and basic argument validation for posix timers.

use crate::{
    scheduler,
    thread::{self, Thread},
    time,
};
use blueos_kconfig::CONFIG_TICKS_PER_SECOND;
use libc::{c_int, c_long, clockid_t, itimerspec, sigevent, time_t, timer_t, timespec, EINVAL};

pub const TIMER_ABSTIME: c_int = 1;
const NS_PER_SEC: i64 = 1_000_000_000;
const NS_PER_MS: u64 = 1_000_000;

pub(crate) const CLOCK_REALTIME: clockid_t = 0;
pub(crate) const CLOCK_MONOTONIC: clockid_t = 1;
pub(crate) const CLOCK_PROCESS_CPUTIME_ID: clockid_t = 2;
pub(crate) const CLOCK_THREAD_CPUTIME_ID: clockid_t = 3;

// Global realtime offset.
use crate::sync::spinlock::SpinLock;
static REALTIME_OFFSET_NS: SpinLock<i64> = SpinLock::new(0);

// add for blueos time type representation in i64 nanoseconds
fn ms_to_ns_saturated(millis: u64) -> i64 {
    let nanos = millis.saturating_mul(NS_PER_MS);
    if nanos > i64::MAX as u64 {
        i64::MAX
    } else {
        nanos as i64
    }
}

fn thread_cpu_cycles(thread: &Thread) -> u64 {
    let mut total = thread.get_cycles();
    // Include the cycles accumulated since the thread started running.
    let now = time::get_sys_cycles();
    total = total.saturating_add(now.saturating_sub(thread.start_cycles()));
    total
}

fn thread_cpu_time_ns(thread: &Thread) -> i64 {
    let millis = time::cycles_to_millis(thread_cpu_cycles(thread));
    ms_to_ns_saturated(millis)
}

fn current_thread_cpu_time_ns() -> i64 {
    let current = scheduler::current_thread();
    thread_cpu_time_ns(&current)
}

fn current_process_cpu_time_ns() -> i64 {
    // calling thread's CPU time as the process-wide accounting(aka. think an not multi-threaded process).
    current_thread_cpu_time_ns()
}

pub(crate) fn monotonic_time_ns() -> i64 {
    let cycles = time::get_sys_cycles();
    let millis = time::cycles_to_millis(cycles);
    ms_to_ns_saturated(millis)
}

pub(crate) fn realtime_time_ns() -> i64 {
    let offset = *REALTIME_OFFSET_NS.lock();
    monotonic_time_ns().saturating_add(offset)
}

pub(crate) fn set_realtime_offset_ns(offset: i64) {
    *REALTIME_OFFSET_NS.lock() = offset;
}

fn ns_to_timespec(total_ns: i64) -> timespec {
    let mut seconds = total_ns / NS_PER_SEC;
    let mut nanoseconds = total_ns % NS_PER_SEC;
    if nanoseconds < 0 {
        seconds -= 1;
        nanoseconds += NS_PER_SEC;
    }
    timespec {
        tv_sec: seconds as time_t,
        tv_nsec: nanoseconds as c_long,
    }
}

fn timespec_to_ns(ts: &timespec) -> Result<i64, c_long> {
    if ts.tv_nsec < 0 || ts.tv_nsec as i64 >= NS_PER_SEC {
        return Err(-EINVAL as c_long);
    }
    let seconds = ts.tv_sec as i64;
    let nanos = ts.tv_nsec as i64;
    seconds
        .checked_mul(NS_PER_SEC)
        .and_then(|base| base.checked_add(nanos))
        .ok_or(-EINVAL as c_long)
}

fn ticks_from_ns(ns: i64) -> usize {
    if ns <= 0 {
        return 0;
    }
    let ticks_per_second = CONFIG_TICKS_PER_SECOND as i64;
    let seconds = ns / NS_PER_SEC;
    let nanos = ns % NS_PER_SEC;

    let ticks_from_seconds = seconds.saturating_mul(ticks_per_second);
    let fractional = (nanos
        .saturating_mul(ticks_per_second)
        .saturating_add(NS_PER_SEC - 1))
        / NS_PER_SEC;

    let total = ticks_from_seconds.saturating_add(fractional);
    match usize::try_from(total) {
        Ok(val) => val,
        Err(_) => usize::MAX,
    }
}

fn sleep_for_ticks(ticks: usize) {
    if ticks == 0 {
        scheduler::yield_me();
    } else {
        scheduler::suspend_me_for(ticks);
    }
}

pub(crate) fn is_supported_clock_id(clock_id: clockid_t) -> bool {
    matches!(
        clock_id,
        CLOCK_REALTIME | CLOCK_MONOTONIC | CLOCK_PROCESS_CPUTIME_ID | CLOCK_THREAD_CPUTIME_ID
    )
}

pub(crate) fn clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> c_long {
    if tp.is_null() {
        return -EINVAL as c_long;
    }
    if !is_supported_clock_id(clk_id) {
        return -EINVAL as c_long;
    }
    let time_ns: i64 = match clk_id {
        CLOCK_REALTIME => realtime_time_ns(),
        CLOCK_MONOTONIC => monotonic_time_ns(),
        CLOCK_PROCESS_CPUTIME_ID => current_process_cpu_time_ns(),
        CLOCK_THREAD_CPUTIME_ID => current_thread_cpu_time_ns(),
        _ => monotonic_time_ns(),
    };
    unsafe {
        *tp = ns_to_timespec(time_ns);
    }
    0
}

// don't allow set CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID, CLOCK_THREAD_CPUTIME_ID
pub(crate) fn clock_settime(clk_id: clockid_t, tp: *const timespec) -> c_long {
    if tp.is_null() {
        return -EINVAL as c_long;
    }
    if clk_id != CLOCK_REALTIME {
        return -EINVAL as c_long;
    }
    let requested = unsafe { &*tp };
    let target_ns = match timespec_to_ns(requested) {
        Ok(ns) => ns,
        Err(errno) => return errno,
    };
    let monotonic_ns = monotonic_time_ns();
    set_realtime_offset_ns(target_ns.saturating_sub(monotonic_ns));
    0
}

fn validate_clock_for_sleep(clock_id: clockid_t) -> bool {
    matches!(clock_id, CLOCK_MONOTONIC | CLOCK_REALTIME)
}

fn remaining_ns_for_absolute(clock_id: clockid_t, target: &timespec) -> Result<i64, c_long> {
    let target_ns = timespec_to_ns(target)?;
    let now_ns = match clock_id {
        CLOCK_REALTIME => realtime_time_ns(),
        CLOCK_MONOTONIC => monotonic_time_ns(),
        _ => return Err(-EINVAL as c_long),
    };
    Ok(target_ns.saturating_sub(now_ns))
}

fn remaining_ns_for_relative(target: &timespec) -> Result<i64, c_long> {
    let ns = timespec_to_ns(target)?;
    if ns < 0 {
        return Err(-EINVAL as c_long);
    }
    Ok(ns)
}

fn clear_remaining_time(rmtp: *mut timespec) {
    if rmtp.is_null() {
        return;
    }
    unsafe {
        (*rmtp).tv_sec = 0;
        (*rmtp).tv_nsec = 0;
    }
}

pub(crate) fn clock_nanosleep(
    clock_id: clockid_t,
    flags: c_int,
    rqtp: *const timespec,
    rmtp: *mut timespec,
) -> c_long {
    if rqtp.is_null() {
        return -EINVAL as c_long;
    }
    if !validate_clock_for_sleep(clock_id) {
        return -EINVAL as c_long;
    }
    let supported_flags = TIMER_ABSTIME;
    if flags & !supported_flags != 0 {
        return -EINVAL as c_long;
    }
    let request = unsafe { &*rqtp };
    let remaining_ns = if (flags & TIMER_ABSTIME) != 0 {
        remaining_ns_for_absolute(clock_id, request)
    } else {
        remaining_ns_for_relative(request)
    };
    let remaining_ns = match remaining_ns {
        Ok(ns) => ns,
        Err(errno) => return errno,
    };
    if remaining_ns <= 0 {
        clear_remaining_time(rmtp);
        return 0;
    }
    let ticks = ticks_from_ns(remaining_ns);
    sleep_for_ticks(ticks);
    clear_remaining_time(rmtp);
    0
}

pub(crate) fn timer_create(
    clock_id: clockid_t,
    evp: *const sigevent,
    timerid: *mut timer_t,
) -> c_long {
    // Stub: accept creation request.
    if timerid.is_null() {
        return -EINVAL as c_long;
    }
    if !matches!(clock_id, CLOCK_REALTIME | CLOCK_MONOTONIC) {
        return -EINVAL as c_long;
    }
    if !evp.is_null() {
        return -EINVAL as c_long;
    }
    unsafe { *timerid = 1 as timer_t };
    0
}

pub(crate) fn timer_delete(timerid: timer_t) -> c_long {
    // Stub: treat any non-zero timerid as deletable.
    if timerid == 0 {
        return -EINVAL as c_long;
    }
    0
}

pub(crate) fn timer_getoverrun(timerid: timer_t) -> c_long {
    // Stub: no overrun accounting.
    if timerid == 0 {
        return -EINVAL as c_long;
    }
    0
}

pub(crate) fn timer_gettime(timerid: timer_t, value: *mut itimerspec) -> c_long {
    if timerid == 0 || value.is_null() {
        return -EINVAL as c_long;
    }
    0
}

pub(crate) fn timer_settime(
    timerid: timer_t,
    flags: c_int,
    value: *const itimerspec,
    ovalue: *mut itimerspec,
) -> c_long {
    // Stub: validate pointers/flags
    if timerid == 0 {
        return -EINVAL as c_long;
    }
    if value.is_null() {
        return -EINVAL as c_long;
    }
    if flags & !TIMER_ABSTIME != 0 {
        return -EINVAL as c_long;
    }
    0
}
