// SPDX-License-Identifier: Apache-2.0 OR MIT

// For now, this only includes values matched in all host platforms supported by QEMU.
// https://www.qemu.org/docs/master/about/build-platforms.html

// TODO: should we expose this as public API of `sys` module?

#![allow(dead_code)]

use core::ffi::c_int;

pub(crate) const EPERM: c_int = 1;
pub(crate) const ENOENT: c_int = 2;
pub(crate) const ESRCH: c_int = 3;
pub(crate) const EINTR: c_int = 4;
pub(crate) const EIO: c_int = 5;
pub(crate) const ENXIO: c_int = 6;
pub(crate) const E2BIG: c_int = 7;
pub(crate) const ENOEXEC: c_int = 8;
pub(crate) const EBADF: c_int = 9;
pub(crate) const ECHILD: c_int = 10;

// pub(crate) const EAGAIN: c_int = 11; // linux-like, windows
// pub(crate) const EDEADLK: c_int = 11; // bsd-like

pub(crate) const ENOMEM: c_int = 12;
pub(crate) const EACCES: c_int = 13;
pub(crate) const EFAULT: c_int = 14;

// pub(crate) const ENOTBLK: c_int = 15; // linux-like, bsd-like

pub(crate) const EBUSY: c_int = 16;
pub(crate) const EEXIST: c_int = 17;
pub(crate) const EXDEV: c_int = 18;
pub(crate) const ENODEV: c_int = 19;
pub(crate) const ENOTDIR: c_int = 20;
pub(crate) const EISDIR: c_int = 21;
pub(crate) const EINVAL: c_int = 22;
pub(crate) const ENFILE: c_int = 23;
pub(crate) const EMFILE: c_int = 24;
pub(crate) const ENOTTY: c_int = 25;

// pub(crate) const ETXTBSY: c_int = 26; // linux-like, bsd-like

pub(crate) const EFBIG: c_int = 27;
pub(crate) const ENOSPC: c_int = 28;
pub(crate) const ESPIPE: c_int = 29;
pub(crate) const EROFS: c_int = 30;
pub(crate) const EMLINK: c_int = 31;
pub(crate) const EPIPE: c_int = 32;
pub(crate) const EDOM: c_int = 33;
pub(crate) const ERANGE: c_int = 34;
