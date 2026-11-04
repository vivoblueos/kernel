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
    c_str::CStr,
    errno::{SysCallFailed, ERRNO},
    syscall::{Sys, Syscall},
};
use core::mem::MaybeUninit;
// Imported under another name: this module defines the *function* `statvfs`,
// and a `use` of the struct of the same name binds it in the value namespace
// too, which collides with the function (E0255).
use libc::{c_char, c_int, c_ulong, dev_t, mode_t, statvfs as StatVfs};

/// Translate the kernel's `struct statfs` into the POSIX `struct statvfs`.
///
/// The two structures describe the same filesystem and agree on almost
/// nothing: `statfs` opens with `f_type` and spells the tail `f_namelen` /
/// `f_flags`, while `statvfs` has no type, spells them `f_namemax` / `f_flag`,
/// and inserts `f_favail`. Passing the `statfs` bytes straight to a
/// `fstatvfs()` caller would therefore have it read every field from the wrong
/// offset - and the structs differ in size (112 vs 80 bytes on rv64), so the
/// call would also write past the end of the caller's object.
///
/// This is the only place either layout is named. `fstatvfs` and `statvfs`
/// both go through it, so the two can never disagree about, say, whether
/// `f_namemax` comes from `f_namelen`.
pub(crate) fn statvfs_from_statfs(raw: &libc::statfs) -> StatVfs {
    StatVfs {
        f_bsize: raw.f_bsize as c_ulong,
        // A filesystem that does not distinguish fragments from blocks reports
        // 0 here. Every POSIX caller multiplies by f_frsize, so a zero would
        // turn the capacity into "none"; falling back to the block size is what
        // other implementations do as well.
        f_frsize: if raw.f_frsize == 0 {
            raw.f_bsize
        } else {
            raw.f_frsize
        } as c_ulong,
        f_blocks: raw.f_blocks,
        f_bfree: raw.f_bfree,
        f_bavail: raw.f_bavail,
        f_files: raw.f_files,
        f_ffree: raw.f_ffree,
        // No per-user quota exists, so everything free is free for the caller.
        f_favail: raw.f_ffree,
        f_fsid: raw.f_fsid as c_ulong,
        f_flag: raw.f_flags as c_ulong,
        f_namemax: raw.f_namelen as c_ulong,
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/chmod.html>.
#[no_mangle]
pub unsafe extern "C" fn chmod(path: *const c_char, mode: mode_t) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::chmod(path, mode).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/fchmod.html>.
#[no_mangle]
pub extern "C" fn fchmod(fildes: c_int, mode: mode_t) -> c_int {
    Sys::fchmod(fildes, mode).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/fstat.html>.
#[no_mangle]
pub unsafe extern "C" fn fstat(fildes: c_int, buf: *mut c_char) -> c_int {
    Sys::fstat(fildes, buf).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/fstatvfs.html>.
#[no_mangle]
pub unsafe extern "C" fn fstatvfs(fildes: c_int, buf: *mut StatVfs) -> c_int {
    Sys::fstatvfs(fildes, buf).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/statvfs.html>.
///
/// newlib ships neither `<sys/statvfs.h>` nor an implementation of either
/// function, so both the declaration (`librs/include/sys/statvfs.h`) and this
/// body are ours. The kernel call underneath is `Statfs`, which fills the
/// Linux `struct statfs`; the translation to POSIX's layout happens after it
/// returns, through the same function `fstatvfs` uses.
#[no_mangle]
pub unsafe extern "C" fn statvfs(path: *const c_char, buf: *mut StatVfs) -> c_int {
    if path.is_null() || buf.is_null() {
        ERRNO.set(libc::EFAULT);
        return -1;
    }
    let path = CStr::from_ptr(path);
    let mut raw = MaybeUninit::<libc::statfs>::zeroed();
    Sys::statfs(path, raw.as_mut_ptr() as *mut c_char)
        .map(|()| {
            // SAFETY: `statfs` returned success, so it filled the struct.
            buf.write(statvfs_from_statfs(&raw.assume_init()));
            0
        })
        .syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/statfs.html>.
#[no_mangle]
pub unsafe extern "C" fn statfs(path: *const c_char, buf: *mut c_char) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::statfs(path, buf).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/mkdir.html>.
#[no_mangle]
pub unsafe extern "C" fn mkdir(path: *const c_char, mode: mode_t) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::mkdir(path, mode).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/mkfifo.html>.
#[no_mangle]
pub unsafe extern "C" fn mkfifo(path: *const c_char, mode: mode_t) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::mkfifo(path, mode).map(|()| 0).syscall_failed()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/mknod.html>.
#[no_mangle]
pub unsafe extern "C" fn mknod(path: *const c_char, mode: mode_t, dev: dev_t) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::mknod(path, mode, dev).map(|()| 0).syscall_failed()
}
