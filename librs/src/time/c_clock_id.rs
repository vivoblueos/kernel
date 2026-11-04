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

//! Clock-id translation across the C ABI boundary.
//!
//! Two numberings meet at `clock_gettime`/`clock_nanosleep`/...:
//!
//! | clock                       | C library (newlib) | kernel (`posix_timers.rs`) |
//! |-----------------------------|--------------------|----------------------------|
//! | `CLOCK_REALTIME`            | 1                  | 0                          |
//! | `CLOCK_MONOTONIC`           | 4                  | 1                          |
//! | `CLOCK_PROCESS_CPUTIME_ID`  | 2                  | 2                          |
//! | `CLOCK_THREAD_CPUTIME_ID`   | 3                  | 3                          |
//!
//! newlib keeps the historical POSIX numbering where `CLOCK_REALTIME` is 1 and
//! `CLOCK_MONOTONIC` is 4; the kernel follows the Linux syscall numbering where
//! they are 0 and 1. A C caller compiled against newlib headers therefore hands
//! the left column to an `extern "C"` entry point, and passing it straight to
//! the syscall swaps the two clocks: `clock_gettime(CLOCK_REALTIME)` silently
//! reads the monotonic clock and `clock_gettime(CLOCK_MONOTONIC)` is rejected
//! with `EINVAL`.
//!
//! This file is shared by both librs crate roots (`lib.rs` through
//! `time/mod.rs`, and `newlib.rs` through `qjs_support.rs`), so it must not
//! depend on anything but `libc`. `newlib.rs` includes it by path.

use libc::clockid_t;

// The C library's numbering. Spelled out instead of using `libc::CLOCK_*`
// because the `libc` crate describes the Linux target, whose values are the
// kernel's - using them here would reintroduce the very confusion this file
// exists to prevent.
pub const C_CLOCK_REALTIME: clockid_t = 1;
pub const C_CLOCK_PROCESS_CPUTIME_ID: clockid_t = 2;
pub const C_CLOCK_THREAD_CPUTIME_ID: clockid_t = 3;
pub const C_CLOCK_MONOTONIC: clockid_t = 4;

// The kernel's numbering, as understood by the clock syscalls.
pub const KERNEL_REALTIME: clockid_t = 0;
pub const KERNEL_MONOTONIC: clockid_t = 1;
pub const KERNEL_PROCESS_CPUTIME_ID: clockid_t = 2;
pub const KERNEL_THREAD_CPUTIME_ID: clockid_t = 3;

/// Translates a clock id that arrived from C into the kernel's numbering.
///
/// `None` means "not a clock this kernel implements"; the caller is expected to
/// fail with `EINVAL`, which is what POSIX requires for an unknown clock id.
pub const fn from_c(clock_id: clockid_t) -> Option<clockid_t> {
    match clock_id {
        C_CLOCK_REALTIME => Some(KERNEL_REALTIME),
        C_CLOCK_MONOTONIC => Some(KERNEL_MONOTONIC),
        C_CLOCK_PROCESS_CPUTIME_ID => Some(KERNEL_PROCESS_CPUTIME_ID),
        C_CLOCK_THREAD_CPUTIME_ID => Some(KERNEL_THREAD_CPUTIME_ID),
        _ => None,
    }
}

/// Inverse of [`from_c`], for reporting a kernel clock back to C.
pub const fn to_c(clock_id: clockid_t) -> Option<clockid_t> {
    match clock_id {
        KERNEL_REALTIME => Some(C_CLOCK_REALTIME),
        KERNEL_MONOTONIC => Some(C_CLOCK_MONOTONIC),
        KERNEL_PROCESS_CPUTIME_ID => Some(C_CLOCK_PROCESS_CPUTIME_ID),
        KERNEL_THREAD_CPUTIME_ID => Some(C_CLOCK_THREAD_CPUTIME_ID),
        _ => None,
    }
}
