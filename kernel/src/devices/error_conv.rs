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

use crate::error::Error;
use embedded_io::ErrorKind;
use libc::*;

impl From<ErrorKind> for Error {
    fn from(error: ErrorKind) -> Self {
        let code = match error {
            // An entity was not found, often a file.
            ErrorKind::NotFound => -ENOENT,
            // The operation lacked the necessary privileges to complete.
            ErrorKind::PermissionDenied => -EACCES,
            // The connection was refused by the remote server.
            ErrorKind::ConnectionRefused => -ECONNREFUSED,
            // The connection was reset by the remote server.
            ErrorKind::ConnectionReset => -ECONNRESET,
            // The connection was aborted (terminated) by the remote server.
            ErrorKind::ConnectionAborted => -ECONNABORTED,
            // The network operation failed because it was not connected yet.
            ErrorKind::NotConnected => -ENOTCONN,
            // A socket address could not be bound because the address is already in
            // use elsewhere.
            ErrorKind::AddrInUse => -EADDRINUSE,
            // A nonexistent interface was requested or the requested address was not
            // local.
            ErrorKind::AddrNotAvailable => -EADDRNOTAVAIL,
            // The operation failed because a pipe was closed.
            ErrorKind::BrokenPipe => -EPIPE,
            // An entity already exists, often a file.
            ErrorKind::AlreadyExists => -EEXIST,
            // A parameter was incorrect.
            ErrorKind::InvalidInput => -EINVAL,
            // Data not valid for the operation were encountered.
            //
            // Unlike [`InvalidInput`], this typically means that the operation
            // parameters were valid, however the error was caused by malformed
            // input data.
            //
            // For example, a function that reads a file into a string will error with
            // `InvalidData` if the file's contents are not valid UTF-8.
            //
            // [`InvalidInput`]: ErrorKind::InvalidInput
            ErrorKind::InvalidData => -EIO,
            // The I/O operation's timeout expired, causing it to be canceled.
            ErrorKind::TimedOut => -ETIMEDOUT,
            // This operation was interrupted.
            //
            // Interrupted operations can typically be retried.
            ErrorKind::Interrupted => -EINTR,
            // This operation is unsupported on this platform.
            //
            // This means that the operation can never succeed.
            ErrorKind::Unsupported => -ENOSYS,
            // An operation could not be completed, because it failed
            // to allocate enough memory.
            ErrorKind::OutOfMemory => -ENOMEM,
            // An attempted write could not write any data.
            ErrorKind::WriteZero => -EIO,
            _ => -EIO,
        };
        Error::from_errno(code)
    }
}
