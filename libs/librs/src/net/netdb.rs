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

use alloc::ffi::CString;
pub use blueos_header::syscalls::NR::{FreeAddrinfo, GetAddrinfo};
use blueos_scal::bk_syscall;

/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getaddrinfo.html>
#[no_mangle]
pub unsafe extern "C" fn getaddrinfo(
    node: *const libc::c_char,
    service: *const libc::c_char,
    hints: *const libc::addrinfo,
    res: *mut *mut libc::addrinfo,
) -> libc::c_int {
    bk_syscall!(GetAddrinfo, node, service, hints, res) as libc::c_int
}

/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/freeaddrinfo.html>
#[no_mangle]
pub unsafe extern "C" fn freeaddrinfo(res: *mut libc::addrinfo) {
    bk_syscall!(FreeAddrinfo, res);
}

/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/gai_strerror.html>
#[no_mangle]
pub unsafe extern "C" fn gai_strerror(errcode: libc::c_int) -> *const libc::c_char {
    let err = CString::new("Unimplement method").unwrap();
    err.as_ptr()
}
