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

use alloc::alloc::{AllocError, LayoutError};
use core::{ffi::CStr, num::TryFromIntError, str::Utf8Error};

pub mod code {
    use libc;
    pub const EOK: super::Error = super::Error(0);
    pub const TRUE: super::Error = super::Error(1);
    pub const FLASE: super::Error = super::Error(0);
    pub const ERROR: super::Error = super::Error(-255);
    pub const ETIMEDOUT: super::Error = super::Error(-libc::ETIMEDOUT);
    pub const ENOSPC: super::Error = super::Error(-libc::ENOSPC);
    pub const ENODATA: super::Error = super::Error(-libc::ENODATA);
    pub const ENOMEM: super::Error = super::Error(-libc::ENOMEM);
    pub const ENOSYS: super::Error = super::Error(-libc::ENOSYS);
    pub const EBUSY: super::Error = super::Error(-libc::EBUSY);
    pub const EIO: super::Error = super::Error(-libc::EIO);
    pub const EINTR: super::Error = super::Error(-libc::EINTR);
    pub const EINVAL: super::Error = super::Error(-libc::EINVAL);
    pub const ENOENT: super::Error = super::Error(-libc::ENOENT);
    pub const ENODEV: super::Error = super::Error(-libc::ENODEV);
    pub const EPERM: super::Error = super::Error(-libc::EPERM);
    pub const EAGAIN: super::Error = super::Error(-libc::EAGAIN);
    pub const EBADF: super::Error = super::Error(-libc::EBADF);
    pub const EEXIST: super::Error = super::Error(-libc::EEXIST);
    pub const ENOTDIR: super::Error = super::Error(-libc::ENOTDIR);
    pub const EISDIR: super::Error = super::Error(-libc::EISDIR);
    pub const ENOTEMPTY: super::Error = super::Error(-libc::ENOTEMPTY);
    pub const ENAMETOOLONG: super::Error = super::Error(-libc::ENAMETOOLONG);
    pub const EACCES: super::Error = super::Error(-libc::EACCES);
    pub const ESPIPE: super::Error = super::Error(-libc::ESPIPE);
    pub const EOVERFLOW: super::Error = super::Error(-libc::EOVERFLOW);
    pub const ELOOP: super::Error = super::Error(-libc::ELOOP);
    pub const EXDEV: super::Error = super::Error(-libc::EXDEV);
    pub const EILSEQ: super::Error = super::Error(-libc::EILSEQ);
    pub const ENOTSUP: super::Error = super::Error(-libc::ENOTSUP);
    pub const ENOTTY: super::Error = super::Error(-libc::ENOTTY);
}

const UNKNOW_STR: &CStr = c"EUNKNOW ";
const EOK_STR: &CStr = c"OK  ";
const ERROR_STR: &CStr = c"ERROR  ";
const ETIMEDOUT_STR: &CStr = c"Timedout  ";
const ENOSPC_STR: &CStr = c"No space left on device  ";
const ENODATA_STR: &CStr = c"No data available  ";
const ENOMEM_STR: &CStr = c"Cannot allocate memory  ";
const ENOSYS_STR: &CStr = c"Function not implemented  ";
const EBUSY_STR: &CStr = c"Device or resource busy  ";
const EIO_STR: &CStr = c"Input/output error  ";
const EINTR_STR: &CStr = c"Interrupted system call  ";
const EINVAL_STR: &CStr = c"Invalid argument  ";
const ENOENT_STR: &CStr = c"No such file or directory  ";
const EPERM_STR: &CStr = c"Operation not permitted  ";
const ENODEV_STR: &CStr = c"No Such Device  ";
const EAGAIN_STR: &CStr = c"Try again  ";
const EBADF_STR: &CStr = c"File descriptor in bad state  ";
const EEXIST_STR: &CStr = c"File exists ";
const ENOTDIR_STR: &CStr = c"Not a directory ";
const EISDIR_STR: &CStr = c"Is a directory ";
const ENOTEMPTY_STR: &CStr = c"Directory not empty ";
const ENAMETOOLONG_STR: &CStr = c"File name too long";
const ESPIPE_STR: &CStr = c"Invalid seek";
const EOVERFLOW_STR: &CStr = c"Value too large to be stored in data type";
const ELOOP_STR: &CStr = c"Too many symbolic links encountered";
const EXDEV_STR: &CStr = c"Cross-device link";
const EILSEQ_STR: &CStr = c"Invalid data";
const ENOTSUP_STR: &CStr = c"Not supported";
const ENOTTY_STR: &CStr = c"Inappropriate ioctl for device";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Error(i32);
static mut ERRNO: Error = Error(0);

impl Error {
    pub fn from_errno(errno: i32) -> Error {
        Error(errno)
    }

    pub fn to_errno(self) -> i32 {
        self.0
    }

    pub fn name(&self) -> &'static CStr {
        match *self {
            code::ERROR => ERROR_STR,
            code::ETIMEDOUT => ETIMEDOUT_STR,
            code::ENOSPC => ENOSPC_STR,
            code::ENODATA => ENODATA_STR,
            code::ENOMEM => ENOMEM_STR,
            code::ENOSYS => ENOSYS_STR,
            code::EBUSY => EBUSY_STR,
            code::EIO => EIO_STR,
            code::EOK => EOK_STR,
            code::EINTR => EINTR_STR,
            code::EINVAL => EINVAL_STR,
            code::ENOENT => ENOENT_STR,
            code::EPERM => EPERM_STR,
            code::EAGAIN => EAGAIN_STR,
            code::EBADF => EBADF_STR,
            code::EEXIST => EEXIST_STR,
            code::ENOTDIR => ENOTDIR_STR,
            code::EISDIR => EISDIR_STR,
            code::ENOTEMPTY => ENOTEMPTY_STR,
            code::ENODEV => ENODEV_STR,
            code::ENAMETOOLONG => ENAMETOOLONG_STR,
            code::ESPIPE => ESPIPE_STR,
            code::EOVERFLOW => EOVERFLOW_STR,
            code::ELOOP => ELOOP_STR,
            code::EXDEV => EXDEV_STR,
            code::EILSEQ => EILSEQ_STR,
            code::ENOTSUP => ENOTSUP_STR,
            code::ENOTTY => ENOTTY_STR,
            _ => UNKNOW_STR,
        }
    }
}

impl From<AllocError> for Error {
    fn from(_: AllocError) -> Error {
        code::ENOMEM
    }
}

impl From<TryFromIntError> for Error {
    fn from(_: TryFromIntError) -> Error {
        code::EINVAL
    }
}

impl From<Utf8Error> for Error {
    fn from(_: Utf8Error) -> Error {
        code::EINVAL
    }
}

impl From<LayoutError> for Error {
    fn from(_: LayoutError) -> Error {
        code::ENOMEM
    }
}

impl From<core::fmt::Error> for Error {
    fn from(_: core::fmt::Error) -> Error {
        code::EINVAL
    }
}

impl From<core::convert::Infallible> for Error {
    fn from(e: core::convert::Infallible) -> Error {
        match e {}
    }
}

impl<T> From<fatfs::Error<T>> for Error {
    fn from(value: fatfs::Error<T>) -> Self {
        match value {
            fatfs::Error::Io(_) => code::EIO,
            fatfs::Error::UnexpectedEof => code::EIO,
            fatfs::Error::WriteZero => code::EIO,
            fatfs::Error::InvalidInput => code::EINVAL,
            fatfs::Error::NotFound => code::ENOENT,
            fatfs::Error::AlreadyExists => code::EEXIST,
            fatfs::Error::DirectoryIsNotEmpty => code::ENOTEMPTY,
            fatfs::Error::CorruptedFileSystem => code::EIO,
            fatfs::Error::NotEnoughSpace => code::ENOSPC,
            fatfs::Error::InvalidFileNameLength => code::EINVAL,
            fatfs::Error::UnsupportedFileNameCharacter => code::EILSEQ,
            _ => code::EIO,
        }
    }
}

pub fn strerror(error: i32) -> *const core::ffi::c_char {
    Error(error).name().as_ptr()
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Convert CStr to str, fallback to error code if conversion fails
        let err_msg = self.name().to_str().unwrap_or("Unknown error");
        write!(f, "Error({}): {}", self.0, err_msg)
    }
}
