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

use core::ffi::{c_int, c_long};

// FIXME: What are their OpenGroup URLs?
pub const _SC_ARG_MAX: c_int = 0;
pub const _SC_CHILD_MAX: c_int = 1;
pub const _SC_CLK_TCK: c_int = 2;
pub const _SC_NGROUPS_MAX: c_int = 3;
pub const _SC_OPEN_MAX: c_int = 4;
pub const _SC_STREAM_MAX: c_int = 5;
pub const _SC_TZNAME_MAX: c_int = 6;
pub const _SC_VERSION: c_int = 29;
pub const _SC_PAGESIZE: c_int = 30;
pub const _SC_PAGE_SIZE: c_int = 30;
pub const _SC_RE_DUP_MAX: c_int = 44;
pub const _SC_NPROCESSORS_ONLN: c_int = 58;
pub const _SC_GETGR_R_SIZE_MAX: c_int = 69;
pub const _SC_GETPW_R_SIZE_MAX: c_int = 70;
pub const _SC_LOGIN_NAME_MAX: c_int = 71;
pub const _SC_TTY_NAME_MAX: c_int = 72;
pub const _SC_SYMLOOP_MAX: c_int = 173;
pub const _SC_HOST_NAME_MAX: c_int = 180;

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sysconf.html>.
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn sysconf(name: c_int) -> c_long {
    // TODO: Real values
    match name {
        _SC_ARG_MAX => 255,
        _SC_CHILD_MAX => 127,
        _SC_CLK_TCK => 100,
        _SC_NGROUPS_MAX => 127,
        _SC_OPEN_MAX => 127,
        _SC_STREAM_MAX => 16,
        _SC_TZNAME_MAX => -1,
        _SC_VERSION => 200809,
        _SC_PAGESIZE => 4096,
        _SC_RE_DUP_MAX => 32767,
        _SC_GETGR_R_SIZE_MAX => -1,
        _SC_GETPW_R_SIZE_MAX => -1,
        _SC_LOGIN_NAME_MAX => 15,
        _SC_TTY_NAME_MAX => 31,
        _SC_SYMLOOP_MAX => -1,
        _SC_HOST_NAME_MAX => 15,
        _SC_NPROCESSORS_ONLN => 1,
        _ => {
            // TODO: Set errno.
            -1
        }
    }
}
