// musl as a whole is licensed under the following standard MIT license:
//
// ----------------------------------------------------------------------
// Copyright © 2005-2020 Rich Felker, et al.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
// ----------------------------------------------------------------------

use core::{cell::Cell, ffi::c_int};
const NUM_ERRNO: usize = 143;
// Use error strings defined in musl/src/errno/__strerror.h.
const fn build_errno_string_table() -> [&'static str; NUM_ERRNO] {
    let mut tbl = ["No error information"; NUM_ERRNO];
    tbl[libc::EILSEQ as usize] = "Illegal byte sequence";
    tbl[libc::EDOM as usize] = "Domain error";
    tbl[libc::ERANGE as usize] = "Result not representable";
    tbl[libc::ENOTTY as usize] = "Not a tty";
    tbl[libc::EACCES as usize] = "Permission denied";
    tbl[libc::EPERM as usize] = "Operation not permitted";
    tbl[libc::ENOENT as usize] = "No such file or directory";
    tbl[libc::ESRCH as usize] = "No such process";
    tbl[libc::EEXIST as usize] = "File exists";
    tbl[libc::EOVERFLOW as usize] = "Value too large for data type";
    tbl[libc::ENOSPC as usize] = "No space left on device";
    tbl[libc::ENOMEM as usize] = "Out of memory";
    tbl[libc::EBUSY as usize] = "Resource busy";
    tbl[libc::EINTR as usize] = "Interrupted system call";
    tbl[libc::EAGAIN as usize] = "Resource temporarily unavailable";
    tbl[libc::ESPIPE as usize] = "Invalid seek";
    tbl[libc::EXDEV as usize] = "Cross-device link";
    tbl[libc::EROFS as usize] = "Read-only file system";
    tbl[libc::ENOTEMPTY as usize] = "Directory not empty";
    tbl[libc::ECONNRESET as usize] = "Connection reset by peer";
    tbl[libc::ETIMEDOUT as usize] = "Operation timed out";
    tbl[libc::ECONNREFUSED as usize] = "Connection refused";
    tbl[libc::EHOSTDOWN as usize] = "Host is down";
    tbl[libc::EHOSTUNREACH as usize] = "Host is unreachable";
    tbl[libc::EADDRINUSE as usize] = "Address in use";
    tbl[libc::EPIPE as usize] = "Broken pipe";
    tbl[libc::EIO as usize] = "I/O error";
    tbl[libc::ENXIO as usize] = "No such device or address";
    tbl[libc::ENODEV as usize] = "No such device";
    tbl[libc::ENOTDIR as usize] = "Not a directory";
    tbl[libc::EISDIR as usize] = "Is a directory";
    tbl[libc::ETXTBSY as usize] = "Text file busy";
    tbl[libc::ENOEXEC as usize] = "Exec format error";
    tbl[libc::EINVAL as usize] = "Invalid argument";
    tbl[libc::E2BIG as usize] = "Argument list too long";
    tbl[libc::ELOOP as usize] = "Symbolic link loop";
    tbl[libc::ENAMETOOLONG as usize] = "Filename too long";
    tbl[libc::ENFILE as usize] = "Too many open files in system";
    tbl[libc::EMFILE as usize] = "No file descriptors available";
    tbl[libc::EBADF as usize] = "Bad file descriptor";
    tbl[libc::ECHILD as usize] = "No child process";
    tbl[libc::EFAULT as usize] = "Bad address";
    tbl[libc::EFBIG as usize] = "File too large";
    tbl[libc::EMLINK as usize] = "Too many links";
    tbl[libc::ENOLCK as usize] = "No locks available";
    tbl[libc::EDEADLK as usize] = "Resource deadlock would occur";
    tbl[libc::ENOTRECOVERABLE as usize] = "State not recoverable";
    tbl[libc::EOWNERDEAD as usize] = "Previous owner died";
    tbl[libc::ECANCELED as usize] = "Operation canceled";
    tbl[libc::ENOSYS as usize] = "Function not implemented";
    tbl[libc::ENOMSG as usize] = "No message of desired type";
    tbl[libc::EIDRM as usize] = "Identifier removed";
    tbl[libc::ENOSTR as usize] = "Device not a stream";
    tbl[libc::ENODATA as usize] = "No data available";
    tbl[libc::ETIME as usize] = "Device timeout";
    tbl[libc::ENOSR as usize] = "Out of streams resources";
    tbl[libc::ENOLINK as usize] = "Link has been severed";
    tbl[libc::EPROTO as usize] = "Protocol error";
    tbl[libc::EBADMSG as usize] = "Bad message";
    tbl[libc::ENOTSOCK as usize] = "Not a socket";
    tbl[libc::EDESTADDRREQ as usize] = "Destination address required";
    tbl[libc::EMSGSIZE as usize] = "Message too large";
    tbl[libc::EPROTOTYPE as usize] = "Protocol wrong type for socket";
    tbl[libc::ENOPROTOOPT as usize] = "Protocol not available";
    tbl[libc::EPROTONOSUPPORT as usize] = "Protocol not supported";
    tbl[libc::ENOTSUP as usize] = "Not supported";
    tbl[libc::EPFNOSUPPORT as usize] = "Protocol family not supported";
    tbl[libc::EAFNOSUPPORT as usize] = "Address family not supported by protocol";
    tbl[libc::EADDRNOTAVAIL as usize] = "Address not available";
    tbl[libc::ENETDOWN as usize] = "Network is down";
    tbl[libc::ENETUNREACH as usize] = "Network unreachable";
    tbl[libc::ENETRESET as usize] = "Connection reset by network";
    tbl[libc::ECONNABORTED as usize] = "Connection aborted";
    tbl[libc::ENOBUFS as usize] = "No buffer space available";
    tbl[libc::EISCONN as usize] = "Socket is connected";
    tbl[libc::ENOTCONN as usize] = "Socket not connected";
    tbl[libc::EALREADY as usize] = "Operation already in progress";
    tbl[libc::EINPROGRESS as usize] = "Operation in progress";
    tbl[libc::ESTALE as usize] = "Stale file handle";
    tbl[libc::EDQUOT as usize] = "Quota exceeded";
    tbl[libc::EMULTIHOP as usize] = "Multihop attempted";
    tbl
}

pub struct Errno(pub c_int);
pub type Result<T, E = Errno> = core::result::Result<T, E>;
/// String representations for the respective `errno` values.
pub const STR_ERROR: [&str; NUM_ERRNO] = build_errno_string_table();

#[thread_local]
pub static ERRNO: Cell<c_int> = Cell::new(0);

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn __errno() -> *mut c_int {
    __errno_location()
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn __errno_location() -> *mut c_int {
    ERRNO.as_ptr()
}

pub trait SysCallFailed<T> {
    fn syscall_failed(self) -> T;
}

impl<T: From<i8>> SysCallFailed<T> for Result<T, Errno> {
    fn syscall_failed(self) -> T {
        match self {
            Self::Ok(v) => v,
            Self::Err(Errno(errno)) => {
                ERRNO.set(errno);
                T::from(-1)
            }
        }
    }
}
