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

//! Deadline arithmetic shared by every POSIX timed-wait interface.
//!
//! POSIX timed waits (`pthread_cond_timedwait`, `pthread_mutex_timedlock`,
//! `sem_timedwait`, and the Issue 8 `*_clockwait` variants) all take an
//! **absolute** deadline expressed on a caller-chosen clock. The kernel's
//! futex syscall, on the other hand, takes a **relative** timeout measured in
//! milliseconds. Converting between the two is error-prone: mixing them up
//! turns a 10 ms wait into "wake up in 1970", or into an immediate return.
//!
//! This module is the single place where that conversion happens:
//!
//! * [`clock_now`] reads the current time of a clock given in **C library
//!   numbering** (newlib's), translating it to the kernel numbering on the
//!   way in.
//! * [`remaining`] turns an absolute deadline into the relative timeout the
//!   kernel expects, clamping at zero.
//! * [`expired`] compares an absolute deadline against the current time.
//!
//! Every "clock" parameter in the POSIX interfaces is a C library clock id.
//! The kernel numbering (Linux-style, `CLOCK_REALTIME == 0`) is an internal
//! detail; see `time/c_clock_id.rs` for the two tables.

use core::ffi::c_int;

use libc::{clockid_t, timespec};

use super::c_clock_id;
use super::clock_gettime_in_kernel_ids;

/// The C library's `CLOCK_REALTIME` (newlib numbering).
pub const C_CLOCK_REALTIME: clockid_t = c_clock_id::C_CLOCK_REALTIME;
/// The C library's `CLOCK_MONOTONIC` (newlib numbering).
pub const C_CLOCK_MONOTONIC: clockid_t = c_clock_id::C_CLOCK_MONOTONIC;

/// Reads the current time of `clock_id`.
///
/// `clock_id` is a **C library** clock id (newlib numbering), matching what a
/// POSIX caller passes to `clock_gettime` and friends. Returns `None` if the
/// clock is not one this kernel implements, which POSIX requires the caller to
/// report as `EINVAL`.
pub fn clock_now(clock_id: clockid_t) -> Option<timespec> {
    let kernel_id = c_clock_id::from_c(clock_id)?;
    let mut ts = timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    if clock_gettime_in_kernel_ids(kernel_id, &mut ts) != 0 {
        return None;
    }
    Some(ts)
}

/// Same as [`clock_now`], but yields the zeroed timespec instead of `None`.
///
/// For call sites that have already validated the clock id and just need a
/// best-effort "now" to compare against.
pub fn clock_now_or_zero(clock_id: clockid_t) -> timespec {
    clock_now(clock_id).unwrap_or(timespec {
        tv_sec: 0,
        tv_nsec: 0,
    })
}

/// Compares two timespecs: `true` when `a` is at or after `b`.
pub fn ts_ge(a: &timespec, b: &timespec) -> bool {
    (a.tv_sec, a.tv_nsec) >= (b.tv_sec, b.tv_nsec)
}

/// `true` when the absolute deadline `deadline` has already passed, measured
/// against `now`.
pub fn expired(now: &timespec, deadline: &timespec) -> bool {
    ts_ge(now, deadline)
}

/// Turns the absolute deadline `deadline` into the relative timeout the
/// kernel's futex syscall expects.
///
/// Returns `None` when the deadline has already passed, so the caller can
/// report `ETIMEDOUT` without going through the kernel at all.
pub fn remaining(now: &timespec, deadline: &timespec) -> Option<timespec> {
    if expired(now, deadline) {
        return None;
    }
    let mut sec = deadline.tv_sec - now.tv_sec;
    let mut nsec = deadline.tv_nsec - now.tv_nsec;
    if nsec < 0 {
        sec -= 1;
        nsec += 1_000_000_000;
    }
    Some(timespec {
        tv_sec: sec,
        tv_nsec: nsec,
    })
}

/// An absolute deadline on a specific clock.
///
/// This is the shape every POSIX timed-wait interface works with: the caller
/// supplies an absolute time on a clock of its choosing, and the deadline has
/// to be turned into the kernel's *relative* millisecond timeout at the last
/// possible moment.
#[derive(Clone, Copy, Debug)]
pub struct Deadline {
    /// C library clock id (newlib numbering) the deadline is expressed on.
    pub clock: clockid_t,
    /// The absolute deadline itself.
    pub at: timespec,
}

impl PartialEq for Deadline {
    fn eq(&self, other: &Self) -> bool {
        self.clock == other.clock && self.at.tv_sec == other.at.tv_sec && self.at.tv_nsec == other.at.tv_nsec
    }
}

impl Eq for Deadline {}

impl Deadline {
    /// Builds a deadline on `clock`.
    pub const fn new(clock: clockid_t, at: timespec) -> Self {
        Self { clock, at }
    }

    /// The relative timeout the kernel futex expects, or `None` if the
    /// deadline has already passed (or the clock is unknown to this kernel).
    pub fn remaining(&self) -> Option<timespec> {
        remaining_on(self.clock, &self.at)
    }

    /// `true` when the deadline has already passed.
    pub fn is_expired(&self) -> bool {
        self.remaining().is_none()
    }
}

/// Convenience wrapper: the relative timeout remaining until `deadline` on
/// `clock_id`, or `None` if the clock is unknown or the deadline has passed.
pub fn remaining_on(clock_id: clockid_t, deadline: &timespec) -> Option<timespec> {
    let now = clock_now(clock_id)?;
    remaining(&now, deadline)
}

/// Validates a POSIX timespec: `tv_nsec` must be in `[0, 1_000_000_000)`.
///
/// Returns `EINVAL` as a `c_int` for the POSIX error-code convention, or `0`
/// when the value is well formed.
pub fn validate_timespec(ts: &timespec) -> c_int {
    if ts.tv_nsec < 0 || ts.tv_nsec >= 1_000_000_000 {
        return libc::EINVAL;
    }
    0
}

/// Validates a clock id.
///
/// POSIX distinguishes "this clock is not supported" (`EINVAL`) from "the
/// deadline has passed" (`ETIMEDOUT`). An unsupported clock therefore has to
/// be rejected at the boundary, before the deadline is ever compared against
/// the current time - otherwise the caller is told the wait timed out when
/// in fact the clock never existed.
pub fn validate_clock(clock_id: clockid_t) -> c_int {
    match c_clock_id::from_c(clock_id) {
        Some(_) => 0,
        None => libc::EINVAL,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Use the project's test attribute: the built-in `#[test]` expands to a
    // `TestDescAndFn`, which does not match this crate's `&[&dyn Fn()]` test
    // runner.
    use blueos_test_macro::test;

    // `tv_sec`/`tv_nsec` are `c_long`, which is 32-bit wide on the 32-bit
    // targets, so the helper casts instead of fixing the width.
    fn ts(sec: i64, nsec: i64) -> timespec {
        timespec {
            tv_sec: sec as _,
            tv_nsec: nsec as _,
        }
    }

    // `libc::timespec` does not implement `PartialEq`, so compare the fields
    // explicitly instead of using `assert_eq!` on `Option<timespec>`.
    fn same_ts(a: Option<timespec>, b: Option<timespec>) -> bool {
        match (a, b) {
            (Some(lhs), Some(rhs)) => lhs.tv_sec == rhs.tv_sec && lhs.tv_nsec == rhs.tv_nsec,
            (None, None) => true,
            _ => false,
        }
    }

    #[test]
    fn remaining_subtracts() {
        let now = ts(10, 500_000_000);
        assert!(same_ts(
            remaining(&now, &ts(12, 100_000_000)),
            Some(ts(1, 600_000_000))
        ));
    }

    #[test]
    fn remaining_borrows_across_seconds() {
        let now = ts(10, 900_000_000);
        assert!(same_ts(
            remaining(&now, &ts(12, 100_000_000)),
            Some(ts(1, 200_000_000))
        ));
    }

    #[test]
    fn remaining_none_when_expired() {
        let now = ts(10, 0);
        assert!(same_ts(remaining(&now, &ts(9, 999_999_999)), None));
        assert!(same_ts(remaining(&now, &ts(10, 0)), None));
    }

    #[test]
    fn expiry_is_inclusive() {
        let now = ts(10, 0);
        assert!(expired(&now, &ts(9, 0)));
        assert!(expired(&now, &ts(10, 0)));
        assert!(!expired(&now, &ts(10, 1)));
    }

    #[test]
    fn timespec_validation() {
        assert_eq!(validate_timespec(&ts(0, 0)), 0);
        assert_eq!(validate_timespec(&ts(0, 999_999_999)), 0);
        assert_eq!(validate_timespec(&ts(0, 1_000_000_000)), libc::EINVAL);
        assert_eq!(validate_timespec(&ts(0, -1)), libc::EINVAL);
    }

    #[test]
    fn clock_validation() {
        // The clocks POSIX requires the Issue 8 timed-wait interfaces to
        // support.
        assert_eq!(validate_clock(C_CLOCK_REALTIME), 0);
        assert_eq!(validate_clock(C_CLOCK_MONOTONIC), 0);
        // An unknown clock is EINVAL, not ETIMEDOUT.
        assert!(validate_clock(9999) == libc::EINVAL);
    }
}
