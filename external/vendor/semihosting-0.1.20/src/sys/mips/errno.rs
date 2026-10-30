// SPDX-License-Identifier: Apache-2.0 OR MIT

// Values are defined in the appendix of Reference Manual.

// TODO: should we expose this as public API of `sys` module?

#![allow(dead_code)]

use core::ffi::c_int;

pub(crate) const EPERM: c_int = 1; // link, unlink
pub(crate) const ENOENT: c_int = 2; // link, unlink, open
pub(crate) const EINTR: c_int = 4; // open, close, read, write
pub(crate) const EIO: c_int = 5; // pwrite, open, close, fstat, pread, read, write
pub(crate) const ENXIO: c_int = 6; // open, pread, pwrite, read, write
pub(crate) const EBADF: c_int = 9; // pwrite, pread, close, lseek, fstat, read, write
pub(crate) const EAGAIN: c_int = 11; // pread, pwrite, read, write
pub(crate) const EWOULDBLOCK: c_int = 11; // pread, pwrite
pub(crate) const ENOMEM: c_int = 12; // open, pread, read
pub(crate) const EACCES: c_int = 13; // pwrite, link, unlink, open, write
pub(crate) const EBUSY: c_int = 16; // unlink,
pub(crate) const EEXIST: c_int = 17; // link, open,
pub(crate) const EXDEV: c_int = 18; // link
pub(crate) const ENOTDIR: c_int = 20; // link, unlink, open
pub(crate) const EISDIR: c_int = 21; // open, pread, read
pub(crate) const EINVAL: c_int = 22; // lseek, pread, pwrite, open, read
pub(crate) const ENFILE: c_int = 23; // open
pub(crate) const EMFILE: c_int = 24; // open
pub(crate) const ETXTBSY: c_int = 26; // unlink, open
pub(crate) const EFBIG: c_int = 27; // pwrite, read, write
pub(crate) const ENOSPC: c_int = 28; // pwrite, link, open, write
pub(crate) const ESPIPE: c_int = 29; // lseek, pread, pwrite, read
pub(crate) const EROFS: c_int = 30; // link, unlink, open
pub(crate) const EMLINK: c_int = 31; // link,
pub(crate) const EPIPE: c_int = 32; // pwrite, write, write
pub(crate) const ERANGE: c_int = 34; // pwrite, write
pub(crate) const ENOSR: c_int = 63; // open
pub(crate) const EBADMSG: c_int = 77; // pread, read
pub(crate) const ENAMETOOLONG: c_int = 91; // link, unlink, open
pub(crate) const ELOOP: c_int = 92; // open, link, unlink
pub(crate) const ECONNRESET: c_int = 104; // pread, pwrite, read
pub(crate) const ENOBUFS: c_int = 105; // pread, pwrite, read, write
pub(crate) const ENETUNREACH: c_int = 114; // pwrite, write
pub(crate) const ENETDOWN: c_int = 115; // pwrite, write
pub(crate) const ETIMEDOUT: c_int = 116; // pread, read
pub(crate) const ENOTCONN: c_int = 128; // pread, read
pub(crate) const EOVERFLOW: c_int = 139; // open, lseek, fstat, pread, read
