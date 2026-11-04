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

//! The explicit file-descriptor operations that POSIX.1-2024 (Issue 8) added:
//! `posix_close`, `posix_devctl` and `posix_getdents`.
//!
//! Issue 8 introduced these three functions to make the intent of a
//! descriptor operation explicit at the call site:
//!
//! * `posix_close(fildes, flag)` states whether the close may be restarted
//!   after a signal (`POSIX_CLOSE_RESTART`), which `close()` leaves
//!   unspecified.
//! * `posix_devctl(fildes, dcmd, data, nbyte, info)` is the standardised
//!   spelling of `ioctl()`, with the argument order and the explicit
//!   in/out data length that `ioctl()` lacks.
//! * `posix_getdents(fildes, buf, nbyte, flags)` reads directory entries in
//!   the POSIX `posix_dent` format, rather than the Linux `dirent` format
//!   that `getdents()` uses, and takes a `flags` argument reserved for
//!   future extension.
//!
//! See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_close.html>,
//! <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_devctl.html> and
//! <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_getdents.html>

use core::ffi::{c_int, c_void};

use libc::{c_char, size_t, ssize_t};

use crate::errno::ERRNO;
use crate::syscall::Syscall;

/// The `flag` argument of `posix_close()` that permits an `EINTR` return.
///
/// POSIX allows an implementation to define `POSIX_CLOSE_RESTART` as 0, in
/// which case `posix_close()` never fails with `EINTR`. This implementation
/// does not restart an interrupted close, so the flag is defined as 0.
pub const POSIX_CLOSE_RESTART: c_int = 0;

/// The layout of a `posix_dent` structure, as returned by `posix_getdents()`.
///
/// POSIX defines `d_name` as a flexible array member, so the structure's size
/// is the size of the fixed part. `d_reclen` gives the number of bytes each
/// entry occupies in the buffer, including padding.
#[repr(C)]
pub struct PosixDent {
    /// The file serial number.
    pub d_ino: libc::ino_t,
    /// The number of bytes this entry occupies in the buffer.
    pub d_reclen: libc::c_ushort,
    /// The file type (`DT_*`).
    pub d_type: libc::c_uchar,
    /// The NUL-terminated file name.
    pub d_name: [c_char; 0],
}

const _: () = {
    // The alignment POSIX requires is "no more restrictive than malloc's",
    // which on every target here is the pointer alignment.
    assert!(
        core::mem::align_of::<PosixDent>() <= core::mem::align_of::<usize>(),
        "posix_dent alignment is too strict"
    );
};

/// Issue 8 `posix_close`: closes `fildes`, with an explicit restart policy.
///
/// With `flag == 0` the function never fails with `EINTR`, which implies
/// that `fildes` is always closed (except for `EBADF`, where the descriptor
/// was invalid to begin with).
///
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_close.html>
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn posix_close(fildes: c_int, flag: c_int) -> c_int {
    // The close itself is never interrupted by a signal in this
    // implementation, so the EINTR case does not arise. An invalid flag is
    // still allowed to fail with EINVAL, but POSIX permits it to succeed
    // instead - closing the descriptor and reporting success is simpler and
    // is explicitly allowed.
    let _ = flag;
    crate::unistd::close(fildes)
}

/// Issue 8 `posix_devctl`: passes a device control command to the driver
/// behind `fildes`.
///
/// `dev_data_ptr` carries `nbyte` bytes to and/or from the driver, and
/// `dev_info_ptr` receives driver-specific additional information.
///
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_devctl.html>
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn posix_devctl(
    fildes: c_int,
    dcmd: c_int,
    dev_data_ptr: *mut c_void,
    nbyte: size_t,
    dev_info_ptr: *mut c_int,
) -> c_int {
    // The kernel's ioctl takes the request as an unsigned long and a single
    // pointer argument, which is exactly what dev_data_ptr provides.
    let request = dcmd as libc::c_ulong;

    let ret = unsafe { crate::syscall::Sys::ioctl(fildes, request, dev_data_ptr) };
    match ret {
        Ok(value) => {
            // The driver may report extra information through dev_info_ptr.
            // POSIX leaves the value driver-dependent; the return value of
            // the ioctl is the primary result, so it is forwarded as-is.
            if !dev_info_ptr.is_null() {
                *dev_info_ptr = value;
            }
            0
        }
        Err(crate::errno::Errno(errno)) => {
            // POSIX has exactly one errno for "this device cannot do that":
            // ENOTSUP. The VFS reaches it through two different numbers -
            // ENOSYS from the default `Device::ioctl` (embedded-io's
            // `Unsupported`), which is what a device that implements no
            // commands at all reports, and ENOTTY from a file with no device
            // behind it. Both mean the request never reached an
            // implementation, so both are reported as ENOTSUP here.
            //
            // ENOSYS in particular is *not* forwarded: it tells a caller that
            // `posix_devctl()` itself is unimplemented, which would make it
            // give up on the API rather than on the one command.
            let errno = match errno {
                libc::ENOSYS | libc::ENOTTY => libc::ENOTSUP,
                other => other,
            };
            // `Sys::ioctl` reports the failure as an `Errno` value; it does
            // not store it in `errno` itself, so that is done here.
            ERRNO.set(errno);
            -1
        }
    }
}

/// Issue 8 `posix_getdents`: reads directory entries into `buf` in the POSIX
/// `posix_dent` format.
///
/// The kernel's `getdents` produces Linux `dirent` records; this function
/// translates them into the POSIX layout on the way out.
///
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/posix_getdents.html>
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn posix_getdents(
    fildes: c_int,
    buf: *mut c_void,
    nbyte: size_t,
    flags: c_int,
) -> ssize_t {
    // POSIX says a strictly conforming application sets flags to zero; other
    // values are implementation-defined bitwise flags. None are defined
    // here, so a non-zero value is rejected rather than silently ignored.
    if flags != 0 {
        ERRNO.set(libc::EINVAL);
        return -1;
    }
    if buf.is_null() || nbyte == 0 {
        ERRNO.set(libc::EINVAL);
        return -1;
    }

    // Read the raw Linux dirents into a scratch buffer, then translate.
    // The scratch buffer is bounded so that a caller cannot make the kernel
    // allocate an unbounded amount of memory.
    const SCRATCH: usize = 4096;
    let mut scratch = [0u8; SCRATCH];
    let to_read = core::cmp::min(nbyte, SCRATCH);

    let read = match crate::syscall::Sys::getdents(fildes, &mut scratch[..to_read]) {
        Ok(read) => read,
        Err(crate::errno::Errno(errno)) => {
            // `Sys::getdents` reports the failure as an `Errno` value; it
            // does not store it in `errno` itself, so that is done here.
            ERRNO.set(errno);
            return -1;
        }
    };    if read == 0 {
        // End of directory.
        return 0;
    }

    // Translate as many entries as fit into the caller's buffer.
    let out = buf as *mut u8;
    let mut written = 0usize;
    let mut offset = 0usize;

    while offset < read {
        // The kernel's `getdents` produces `struct dirent` records. The
        // kernel crate asserts that its own `Dirent` has the same field
        // offsets as `libc::dirent`, so parsing with the libc type is safe
        // and does not depend on hard-coded byte offsets.
        if read - offset < core::mem::size_of::<libc::dirent>() {
            break;
        }
        let entry = scratch.as_ptr().add(offset).cast::<libc::dirent>();
        let d_ino = unsafe { (*entry).d_ino };
        let d_reclen = unsafe { (*entry).d_reclen } as usize;
        let d_type = unsafe { (*entry).d_type };
        let d_namlen = unsafe { (*entry).d_namlen } as usize;

        if d_reclen == 0 || offset + d_reclen > read {
            break;
        }
        let name_offset = core::mem::offset_of!(libc::dirent, d_name);
        let name_start = offset + name_offset;
        let name_end = core::cmp::min(name_start + d_namlen, offset + d_reclen);
        let name = &scratch[name_start..name_end];

        // The POSIX entry is: d_ino (8), d_reclen (2), d_type (1), then the
        // name plus its NUL, padded so that the next entry is aligned.
        let header = core::mem::size_of::<PosixDent>();
        let name_len = name.len() + 1;
        let entry_len = align_up(header + name_len, core::mem::align_of::<PosixDent>());

        if written + entry_len > nbyte {
            // No more room for another entry. POSIX requires that at least
            // one entry is produced when the buffer is large enough, so this
            // is only acceptable once at least one entry has been written.
            break;
        }

        let out_entry = out.add(written);
        // d_ino
        write_u64(out_entry as *mut u8, d_ino as u64);
        // d_reclen
        (out_entry as *mut u8).add(8).cast::<libc::c_ushort>().write_unaligned(entry_len as u16);
        // d_type
        *out_entry.add(10) = d_type;
        // d_name
        core::ptr::copy_nonoverlapping(name.as_ptr(), out_entry.add(header), name.len());
        *out_entry.add(header + name.len()) = 0;

        written += entry_len;
        offset += d_reclen;
    }

    if written == 0 {
        // The buffer was too small for even a single entry.
        ERRNO.set(libc::EINVAL);
        return -1;
    }

    written as ssize_t
}

/// Rounds `value` up to a multiple of `align`.
const fn align_up(value: usize, align: usize) -> usize {
    (value + align - 1) & !(align - 1)
}

/// Reads a little-endian `u64` from `buf` at `offset`.
#[allow(dead_code)]
fn read_u64(buf: &[u8], offset: usize) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&buf[offset..offset + 8]);
    u64::from_le_bytes(bytes)
}

/// Reads a little-endian `u16` from `buf` at `offset`.
#[allow(dead_code)]
fn read_u16(buf: &[u8], offset: usize) -> u16 {
    let mut bytes = [0u8; 2];
    bytes.copy_from_slice(&buf[offset..offset + 2]);
    u16::from_le_bytes(bytes)
}

/// Writes a little-endian `u64` to `buf`.
fn write_u64(buf: *mut u8, value: u64) {
    let bytes = value.to_le_bytes();
    unsafe { buf.cast::<[u8; 8]>().write_unaligned(bytes) };
}
