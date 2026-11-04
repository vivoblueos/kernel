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

//! Bridging pointers that arrive in syscall arguments to kernel-usable memory.
//!
//! # Why this exists
//!
//! A syscall handler runs in **M-mode**, where `satp` has no effect: the
//! address it dereferences is a *physical* address. While every caller was a
//! kernel thread that was harmless — the pointer really was a kernel pointer.
//! The moment U-mode exists it becomes a privilege-escalation primitive:
//! `write(fd, 0x8000_0000, 16)` would read secure memory, and
//! `stat(path, 0x0)` would let the caller write a `struct stat` anywhere in
//! physical memory.
//!
//! So every pointer below the syscall boundary goes through this module. It
//! does two things:
//!
//! 1. decides whether the argument is a *user* pointer (the current thread has
//!    an address space) or a *kernel* pointer (it does not), and
//! 2. for user pointers, resolves the page table, demand-paging the range
//!    first, then copies through a bounce buffer.
//!
//! # Why a bounce buffer and not a mapped slice
//!
//! The kernel could temporarily map user pages into kernel space, but that
//! means touching the kernel's own tables on every `read`, and getting the
//! unmap exactly right on every early return. A bounce buffer is one `alloc`
//! for a buffer that is about to be copied anyway, and it cannot be left
//! dangling. Kernel callers keep the zero-copy path, so nothing that worked
//! before pays for this.
//!
//! # What is *not* covered
//!
//! `ioctl` still passes `arg` through as a raw `usize`: the request number
//! decides whether it is a pointer, an integer, or a struct, and each driver
//! interprets it itself. Terminals are the only users today and they are
//! reached through `SYS_ioctl` from libc; that argument needs typing before a
//! U-mode process can call `tcgetattr` safely. Tracked separately.

use crate::error::{code, Error};
use alloc::{string::String, vec, vec::Vec};
use core::ffi::{c_char, CStr};

/// Largest single transfer moved through the bounce buffer.
///
/// `read`/`write` are allowed to return short, so clamping here is legal and
/// costs only a second syscall for a very large buffer. It also bounds the
/// kernel allocation a hostile `count` can trigger.
pub const MAX_XFER: usize = 256 * 1024;

/// Longest path or string accepted from user space, including its terminator.
pub const MAX_PATH: usize = 4096;

/// Whether the calling thread runs inside a user address space.
///
/// False for kernel threads, including the ones the in-kernel test harness
/// creates; their pointers are kernel addresses and are dereferenced directly.
#[cfg(target_arch = "riscv64")]
pub fn in_user_space() -> bool {
    crate::user::current_root().is_some()
}

/// See the 64-bit variant. No other target has a user/kernel split yet, so
/// every pointer here is a kernel pointer.
#[cfg(not(target_arch = "riscv64"))]
pub fn in_user_space() -> bool {
    false
}

// The three calls into `crate::user` are wrapped rather than open-coded so the
// type-checker sees them only on a target that has the module. `in_user_space`
// is a constant `false` elsewhere, which makes the branch dead but does not
// make it disappear before name resolution.

#[cfg(target_arch = "riscv64")]
fn user_cstr(ptr: usize) -> Result<String, Error> {
    crate::user::copy_cstr_from_user(ptr, MAX_PATH).map_err(|_| code::EFAULT)
}

#[cfg(target_arch = "riscv64")]
fn user_read(dst: &mut [u8], src: usize) -> Result<(), Error> {
    crate::user::copy_from_user(dst, src).map_err(|_| code::EFAULT)
}

#[cfg(target_arch = "riscv64")]
fn user_write(dst: usize, src: &[u8]) -> Result<(), Error> {
    crate::user::copy_to_user(dst, src).map_err(|_| code::EFAULT)
}

#[cfg(not(target_arch = "riscv64"))]
fn user_cstr(_ptr: usize) -> Result<String, Error> {
    Err(code::EFAULT)
}

#[cfg(not(target_arch = "riscv64"))]
fn user_read(_dst: &mut [u8], _src: usize) -> Result<(), Error> {
    Err(code::EFAULT)
}

#[cfg(not(target_arch = "riscv64"))]
fn user_write(_dst: usize, _src: &[u8]) -> Result<(), Error> {
    Err(code::EFAULT)
}

/// Read a NUL-terminated string the caller passed in.
///
/// Returns the string without its terminator. Invalid UTF-8 is `EILSEQ` rather
/// than a lossy conversion: a path that silently changes bytes is a path that
/// opens the wrong file.
pub fn cstr(ptr: *const c_char) -> Result<String, Error> {
    if in_user_space() {
        return user_cstr(ptr as usize);
    }
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    // SAFETY: a kernel caller's pointer is a real C string by the same contract
    // that held before U-mode existed.
    unsafe { CStr::from_ptr(ptr) }
        .to_str()
        .map(String::from)
        .map_err(|_| code::EILSEQ)
}

/// Copy `len` bytes from the caller's buffer into a kernel slice.
///
/// The slice is filled completely; a short copy is an error, not a partial
/// read, because the caller has already decided how many bytes it wants.
pub fn read_bytes(ptr: *const u8, dst: &mut [u8]) -> Result<(), Error> {
    if dst.is_empty() {
        return Ok(());
    }
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    if in_user_space() {
        return user_read(dst, ptr as usize);
    }
    // SAFETY: kernel pointer, non-overlapping by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(ptr, dst.as_mut_ptr(), dst.len()) };
    Ok(())
}

/// Copy `src` into the caller's buffer.
pub fn write_bytes(ptr: *mut u8, src: &[u8]) -> Result<(), Error> {
    if src.is_empty() {
        return Ok(());
    }
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    if in_user_space() {
        return user_write(ptr as usize, src);
    }
    // SAFETY: kernel pointer, non-overlapping by the caller's contract.
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), ptr, src.len()) };
    Ok(())
}

/// Write one `#[repr(C)]` value out to the caller's buffer.
///
/// Every `struct stat`-shaped argument lands here. The size written is the
/// type's own, which is asserted against `libc`'s at the definition site, so a
/// mismatch with the C library is a compile error rather than a handful of
/// clobbered bytes at run time.
pub fn write_struct<T>(ptr: *mut T, val: &T) -> Result<(), Error> {
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    // SAFETY: `val` is a live, fully initialised `T`.
    let bytes =
        unsafe { core::slice::from_raw_parts(val as *const T as *const u8, core::mem::size_of::<T>()) };
    write_bytes(ptr as *mut u8, bytes)
}

/// Read one `#[repr(C)]` value from the caller's buffer.
///
/// The mirror of [`write_struct`], for driver `ioctl` arguments such as
/// `struct termios`. A kernel caller's pointer is dereferenced directly; a
/// U-mode caller's is demand-paged and copied through the bounce buffer, so
/// an address the caller does not own is `EFAULT` rather than a privileged
/// read.
pub fn read_struct<T>(ptr: *const T) -> Result<T, Error> {
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    let mut val = core::mem::MaybeUninit::<T>::uninit();
    // SAFETY: `val` is `size_of::<T>()` bytes of writable storage and
    // `read_bytes` fills it completely or returns an error.
    let dst = unsafe {
        core::slice::from_raw_parts_mut(val.as_mut_ptr() as *mut u8, core::mem::size_of::<T>())
    };
    read_bytes(ptr as *const u8, dst)?;
    // SAFETY: every byte of `val` was just written by `read_bytes`.
    Ok(unsafe { val.assume_init() })
}

/// Run `f` over a buffer destined for the caller, then publish the bytes it
/// produced.
///
/// `f` returns how many bytes it wrote; only those are copied out. This is the
/// `read`/`getdents` shape: the callee decides how much of the buffer it filled.
pub fn with_out<F>(ptr: *mut u8, len: usize, f: F) -> Result<usize, Error>
where
    F: FnOnce(&mut [u8]) -> Result<usize, Error>,
{
    if len == 0 {
        return Ok(0);
    }
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    if !in_user_space() {
        // SAFETY: kernel pointer, valid for `len` bytes by the caller's
        // contract — the same assumption this code made before U-mode existed.
        let slice = unsafe { core::slice::from_raw_parts_mut(ptr, len) };
        return f(slice);
    }
    let mut bounce = vec![0u8; len];
    let used = f(&mut bounce)?;
    write_bytes(ptr, &bounce[..used])?;
    Ok(used)
}

/// Run `f` over a copy of the caller's buffer.
///
/// The inverse of [`with_out`], for `write` and friends. A kernel caller still
/// gets a copy rather than a borrowed slice: `f` may block (a socket write
/// can), and a slice into another thread's stack would then be a reference
/// into memory that thread is free to reuse.
pub fn with_in<F>(ptr: *const u8, len: usize, f: F) -> Result<isize, Error>
where
    F: FnOnce(&[u8]) -> Result<isize, Error>,
{
    if len == 0 {
        return Ok(0);
    }
    if ptr.is_null() {
        return Err(code::EINVAL);
    }
    if !in_user_space() {
        // SAFETY: kernel pointer, valid for `len` bytes.
        let slice = unsafe { core::slice::from_raw_parts(ptr, len) };
        return f(slice);
    }
    let mut bounce = vec![0u8; len];
    read_bytes(ptr, &mut bounce)?;
    f(&bounce)
}

/// Read a caller-provided array of pointers-to-strings, as `execve` takes.
///
/// Stops at the first NULL, at `max_entries`, or when an entry cannot be read;
/// a vector that is not terminated within the cap is `E2BIG`, which is what
/// Linux reports for the same situation.
pub fn cstr_vec(ptr: *const *const c_char, max_entries: usize) -> Result<Vec<String>, Error> {
    let mut out = Vec::new();
    if ptr.is_null() {
        return Ok(out);
    }
    for i in 0..max_entries {
        let slot = (ptr as usize)
            .checked_add(i * core::mem::size_of::<usize>())
            .ok_or(code::EINVAL)?;
        let mut raw = [0u8; core::mem::size_of::<usize>()];
        read_bytes(slot as *const u8, &mut raw)?;
        let entry = usize::from_ne_bytes(raw);
        if entry == 0 {
            return Ok(out);
        }
        out.push(cstr(entry as *const c_char)?);
    }
    Err(code::E2BIG)
}
