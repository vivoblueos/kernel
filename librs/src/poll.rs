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

//! POSIX `poll()`, `ppoll()` and `select()` - input/output multiplexing.
//!
//! The `struct pollfd` layout and the `POLL*` bit values match the newlib
//! `<poll.h>` shim in `external/quickjs-ng/bk_include/poll.h`, because the C
//! caller and the kernel have to agree on both. The `fd_set` layout matches
//! newlib's own `<sys/select.h>`: `FD_SETSIZE` 64, one bit per descriptor.

use super::errno::ERRNO;
use blueos_header::syscalls::NR::{Poll, PPoll, Select};
use blueos_scal::bk_syscall;
use core::ffi::{c_int, c_long, c_short, c_uint, c_ulong, c_void};
use libc::{sigset_t, timespec, timeval};

/// The C `nfds_t` from the shim: an `unsigned int`.
#[allow(non_camel_case_types)]
pub type nfds_t = c_uint;

/// The C `struct pollfd`, in the layout newlib's shim declares.
///
/// ```text
/// struct pollfd {
///     int   fd;        // offset 0, 4 bytes
///     short events;    // offset 4, 2 bytes
///     short revents;   // offset 6, 2 bytes
/// };                   // size 8
/// ```
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
#[allow(non_camel_case_types)]
pub struct pollfd {
    pub fd: c_int,
    pub events: c_short,
    pub revents: c_short,
}

// Requested / returned event bits. The values are the ones the shim
// declares; the kernel has to use the same bit positions.
pub const POLLIN: c_short = 0x0001;
pub const POLLPRI: c_short = 0x0002;
pub const POLLOUT: c_short = 0x0004;
pub const POLLERR: c_short = 0x0008;
pub const POLLHUP: c_short = 0x0010;
pub const POLLNVAL: c_short = 0x0020;

/// POSIX `poll()`.
///
/// Scans the `nfds` descriptors in `fds` for the events each entry asks for
/// in `events`, and writes what is actually ready into `revents`. Returns the
/// number of entries with a non-zero `revents`.
///
/// `timeout` is in milliseconds: zero returns after the scan, a negative
/// value waits forever, and a positive value gives up after that long. A
/// signal received before any event makes the call return -1 with `errno` set
/// to `EINTR`.
#[no_mangle]
pub unsafe extern "C" fn poll(fds: *mut pollfd, nfds: nfds_t, timeout: c_int) -> c_int {
    let ret = bk_syscall!(Poll, fds as *mut c_void, nfds as usize, timeout) as c_long;
    if ret < 0 {
        ERRNO.set(-ret as c_int);
        return -1;
    }
    ret as c_int
}

/// POSIX `ppoll()`.
///
/// `poll()` with the timeout expressed as a `struct timespec` interval and
/// with the thread's signal mask replaced by `sigmask` for the duration of
/// the wait. A null `timeout` waits forever; a negative one is an error here,
/// unlike `poll()` where it also means "forever".
#[no_mangle]
pub unsafe extern "C" fn ppoll(
    fds: *mut pollfd,
    nfds: nfds_t,
    timeout: *const timespec,
    sigmask: *const sigset_t,
) -> c_int {
    let ret = bk_syscall!(
        PPoll,
        fds as *mut c_void,
        nfds as usize,
        timeout as usize,
        sigmask as usize
    ) as c_long;
    if ret < 0 {
        ERRNO.set(-ret as c_int);
        return -1;
    }
    ret as c_int
}

/// `FD_SETSIZE` as newlib's `<sys/select.h>` defines it.
///
/// The kernel uses the same value and the same `unsigned long` bitmap layout,
/// so `select()` can copy the sets across the syscall boundary unchanged.
pub const FD_SETSIZE: c_int = 64;

const FD_SET_BITS: usize = core::mem::size_of::<c_ulong>() * 8;
const FD_SET_WORDS: usize = FD_SETSIZE as usize / FD_SET_BITS;

/// The C `fd_set` as newlib lays it out.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
#[allow(non_camel_case_types)]
pub struct fd_set {
    pub fds_bits: [c_ulong; FD_SET_WORDS],
}

/// POSIX `select()`.
///
/// Waits until one of the descriptors in `readfds`, `writefds` or `exceptfds`
/// is ready, or until `timeout` expires. On return the sets name the ready
/// descriptors and the result is how many there are; `timeout` is the usual
/// `struct timeval`, with NULL meaning "wait forever". An unopened descriptor
/// gives -1 with `errno` set to `EBADF`.
#[no_mangle]
pub unsafe extern "C" fn select(
    nfds: c_int,
    readfds: *mut fd_set,
    writefds: *mut fd_set,
    exceptfds: *mut fd_set,
    timeout: *mut timeval,
) -> c_int {
    let ret = bk_syscall!(
        Select,
        nfds,
        readfds as usize,
        writefds as usize,
        exceptfds as usize,
        timeout as usize
    ) as c_long;
    if ret < 0 {
        ERRNO.set(-ret as c_int);
        return -1;
    }
    ret as c_int
}
