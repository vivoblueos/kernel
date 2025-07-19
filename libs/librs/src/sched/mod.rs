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
    errno::SysCallFailed,
    syscall::{Sys, Syscall},
};
use libc::{c_int, pid_t, timespec};

#[allow(non_camel_case_types)]
pub struct sched_param {
    pub sched_priority: c_int,
}

pub const SCHED_FIFO: c_int = 0;
pub const SCHED_RR: c_int = 1;
pub const SCHED_OTHER: c_int = 2;

#[no_mangle]
pub extern "C" fn sched_get_priority_max(policy: c_int) -> c_int {
    Sys::sched_get_priority_max(policy)
}
#[no_mangle]
pub extern "C" fn sched_get_priority_min(policy: c_int) -> c_int {
    Sys::sched_get_priority_min(policy)
}

#[no_mangle]
pub unsafe extern "C" fn sched_rr_get_interval(pid: pid_t, time: *mut timespec) -> c_int {
    Sys::sched_rr_get_interval(pid, time)
        .map(|_| 0)
        .syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn sched_setscheduler(
    _pid: pid_t,
    _policy: c_int,
    _param: *const sched_param,
) -> c_int {
    // POSIX support scheduler in pthread* functions, just return error value
    -1
}
#[no_mangle]
pub extern "C" fn sched_yield() -> c_int {
    Sys::sched_yield().map(|()| 0).syscall_failed()
}
