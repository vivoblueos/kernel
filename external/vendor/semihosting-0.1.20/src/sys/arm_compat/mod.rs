// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Low-level access to semihosting interfaces for Arm (AArch32 and AArch64) and
//! RISC-V (which supports Arm-compatible semihosting interfaces).
//!
//! Refs:
//! - Semihosting for AArch32 and AArch64 <https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst>
//! - RISC-V Semihosting <https://github.com/riscv-non-isa/riscv-semihosting/blob/1.0-rc2/riscv-semihosting.adoc>
//! - <https://github.com/qemu/qemu/blob/v9.2.0/semihosting/arm-compat-semi.c>
//! - <https://github.com/espressif/openocd-esp32/blob/HEAD/src/target/espressif/esp_xtensa_semihosting.c>

#![allow(clippy::missing_safety_doc, clippy::undocumented_unsafe_blocks)] // TODO

pub(crate) mod errno;
#[cfg(feature = "fs")]
pub(crate) mod fs;
pub mod syscall;

use core::{
    ffi::{CStr, c_void},
    mem::{self, MaybeUninit},
};

use self::syscall::{OperationNumber, ParamRegR, ParamRegW, syscall, syscall_readonly, syscall0};
use crate::{
    fd::{BorrowedFd, OwnedFd, RawFd},
    io::{Error, RawOsError, Result},
};

#[derive(Debug, Clone, Copy)]
#[repr(usize)]
#[non_exhaustive]
pub enum ExitReason {
    // Reason codes related to hardware exceptions:
    ADP_Stopped_BranchThroughZero = 0x20000,
    ADP_Stopped_UndefinedInstr = 0x20001,
    ADP_Stopped_SoftwareInterrupt = 0x20002,
    ADP_Stopped_PrefetchAbort = 0x20003,
    ADP_Stopped_DataAbort = 0x20004,
    ADP_Stopped_AddressException = 0x20005,
    ADP_Stopped_IRQ = 0x20006,
    ADP_Stopped_FIQ = 0x20007,

    // Reason codes related to software events:
    ADP_Stopped_BreakPoint = 0x20020,
    ADP_Stopped_WatchPoint = 0x20021,
    ADP_Stopped_StepComplete = 0x20022,
    ADP_Stopped_RunTimeErrorUnknown = 0x20023,
    ADP_Stopped_InternalError = 0x20024,
    ADP_Stopped_UserInterruption = 0x20025,
    ADP_Stopped_ApplicationExit = 0x20026,
    ADP_Stopped_StackOverflow = 0x20027,
    ADP_Stopped_DivisionByZero = 0x20028,
    ADP_Stopped_OSSpecific = 0x20029,
}

// Refs: https://github.com/openocd-org/openocd/blob/HEAD/src/target/semihosting_common.c
#[derive(Debug, Clone, Copy)]
#[repr(usize)]
#[non_exhaustive]
pub enum OpenMode {
    /// `fopen` mode: `r`<br>
    /// `O_*` flags: `O_RDONLY`
    RDONLY = 0,
    /// `fopen` mode: `rb`<br>
    /// `O_*` flags: `O_RDONLY | O_BINARY`
    RDONLY_BINARY = 1,
    /// `fopen` mode: `r+`<br>
    /// `O_*` flags: `O_RDWR`
    RDWR = 2,
    /// `fopen` mode: `r+b`<br>
    /// `O_*` flags: `O_RDWR | O_BINARY`
    RDWR_BINARY = 3,
    /// `fopen` mode: `w`<br>
    /// `O_*` flags: `O_WRONLY | O_CREAT | O_TRUNC`
    WRONLY_TRUNC = 4,
    /// `fopen` mode: `wb`<br>
    /// `O_*` flags: `O_WRONLY | O_CREAT | O_TRUNC | O_BINARY`
    WRONLY_TRUNC_BINARY = 5,
    /// `fopen` mode: `w+`<br>
    /// `O_*` flags: `O_RDWR | O_CREAT | O_TRUNC`
    RDWR_TRUNC = 6,
    /// `fopen` mode: `w+b`<br>
    /// `O_*` flags: `O_RDWR | O_CREAT | O_TRUNC | O_BINARY`
    RDWR_TRUNC_BINARY = 7,
    /// `fopen` mode: `a`<br>
    /// `O_*` flags: `O_WRONLY | O_CREAT | O_APPEND`
    WRONLY_APPEND = 8,
    /// `fopen` mode: `ab`<br>
    /// `O_*` flags: `O_WRONLY | O_CREAT | O_APPEND | O_BINARY`
    WRONLY_APPEND_BINARY = 9,
    /// `fopen` mode: `a+`<br>
    /// `O_*` flags: `O_RDWR | O_CREAT | O_APPEND`
    RDWR_APPEND = 10,
    /// `fopen` mode: `a+b`<br>
    /// `O_*` flags: `O_RDWR | O_CREAT | O_APPEND | O_BINARY`
    RDWR_APPEND_BINARY = 11,
}

#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct HeapInfo {
    pub heap_base: *mut c_void,
    pub heap_limit: *mut c_void,
    pub stack_base: *mut c_void,
    pub stack_limit: *mut c_void,
}

#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct CommandLine {
    pub ptr: *mut u8,
    pub size: usize,
}

/// [SYS_CLOCK (0x10)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-clock-0x10)
pub fn sys_clock() -> Result<usize> {
    let res = unsafe { syscall0(OperationNumber::SYS_CLOCK) };
    if res.int() == -1 { Err(Error::from_raw_os_error(sys_errno())) } else { Ok(res.usize()) }
}

/// [SYS_CLOSE (0x02)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-close-0x02)
pub unsafe fn sys_close(fd: RawFd) -> Result<()> {
    let args = [ParamRegR::raw_fd(fd)];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_CLOSE, ParamRegR::block(&args)) };
    if res.usize() == 0 {
        Ok(())
    } else {
        debug_assert_eq!(res.int(), -1);
        Err(Error::from_raw_os_error(sys_errno()))
    }
}
pub(crate) use self::sys_close as close;

/// [SYS_ELAPSED (0x30)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-elapsed-0x30)
pub fn sys_elapsed() -> Result<u64> {
    // On 32-bit, the parameter is a pointer to two 32-bit field data block
    // On 64-bit, the parameter is a pointer to one 64-bit field data block
    let mut args = [0_u64];
    let res = unsafe { syscall(OperationNumber::SYS_ELAPSED, ParamRegW::ref_(&mut args)) };
    if res.usize() == 0 {
        Ok(args[0])
    } else {
        debug_assert_eq!(res.int(), -1);
        Err(Error::from_raw_os_error(sys_errno()))
    }
}

/// [SYS_ERRNO (0x13)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-errno-0x13)
pub fn sys_errno() -> RawOsError {
    let res = unsafe { syscall0(OperationNumber::SYS_ERRNO) };
    res.errno()
}

#[allow(clippy::cast_sign_loss)]
pub(crate) fn exit(code: i32) {
    // TODO: check sh_ext_exit_extended first
    sys_exit_extended(ExitReason::ADP_Stopped_ApplicationExit, code as isize as usize);
    // If SYS_EXIT_EXTENDED is not supported, above call doesn't exit program,
    // so try again with SYS_EXIT.
    let reason = match code {
        0 => ExitReason::ADP_Stopped_ApplicationExit,
        _ => ExitReason::ADP_Stopped_RunTimeErrorUnknown,
    };
    sys_exit(reason);
}
/// [SYS_EXIT (0x18)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-exit-0x18)
pub fn sys_exit(reason: ExitReason) {
    #[cfg(target_pointer_width = "32")]
    let arg = ParamRegR::usize(reason as usize);
    #[cfg(target_pointer_width = "64")]
    let args = [ParamRegR::usize(reason as usize), ParamRegR::usize(0)];
    #[cfg(target_pointer_width = "64")]
    let arg = ParamRegR::block(&args);
    unsafe {
        syscall_readonly(OperationNumber::SYS_EXIT, arg);
    }
}

/// [SYS_EXIT_EXTENDED (0x20)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-exit-extended-0x20)
pub fn sys_exit_extended(reason: ExitReason, subcode: usize) {
    let args = [ParamRegR::usize(reason as usize), ParamRegR::usize(subcode)];
    #[cfg(target_pointer_width = "32")]
    let number = OperationNumber::SYS_EXIT_EXTENDED;
    // On 64-bit system, SYS_EXIT_EXTENDED call is identical to the behavior of the mandatory SYS_EXIT.
    #[cfg(target_pointer_width = "64")]
    let number = OperationNumber::SYS_EXIT;
    unsafe {
        syscall_readonly(number, ParamRegR::block(&args));
    }
}

/// [SYS_FLEN (0x0C)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-flen-0x0c)
pub fn sys_flen(fd: BorrowedFd<'_>) -> Result<usize> {
    let args = [ParamRegR::fd(fd)];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_FLEN, ParamRegR::block(&args)) };
    if res.int() == -1 { Err(Error::from_raw_os_error(sys_errno())) } else { Ok(res.usize()) }
}

/// [SYS_GET_CMDLINE (0x15)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-get-cmdline-0x15)
///
/// # Safety
///
/// CommandLine::ptr must be valid for at least the size specified in CommandLine::size.
pub unsafe fn sys_get_cmdline(cmdline: &mut CommandLine) -> Result<()> {
    let res = unsafe { syscall(OperationNumber::SYS_GET_CMDLINE, ParamRegW::ref_(cmdline)) };
    if res.usize() == 0 {
        Ok(())
    } else {
        debug_assert_eq!(res.int(), -1);
        Err(Error::from_raw_os_error(sys_errno()))
    }
}

/// [SYS_HEAPINFO (0x16)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-heapinfo-0x16)
pub fn sys_heapinfo() -> HeapInfo {
    let mut buf: HeapInfo = unsafe { mem::zeroed() };
    unsafe {
        syscall(OperationNumber::SYS_HEAPINFO, ParamRegW::ref_(&mut buf));
    }
    buf
}

/// [SYS_ISERROR (0x08)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-iserror-0x08)
pub fn sys_iserror(res: isize) -> bool {
    let args = [ParamRegR::isize(res)];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_ISERROR, ParamRegR::block(&args)) };
    res.usize() != 0
}

/// [SYS_ISTTY (0x09)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-istty-0x09)
pub fn sys_istty(fd: BorrowedFd<'_>) -> Result<bool> {
    let args = [ParamRegR::fd(fd)];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_ISTTY, ParamRegR::block(&args)) };
    match res.usize() {
        1 => Ok(true),
        0 => Ok(false),
        _ => Err(Error::from_raw_os_error(sys_errno())), // TODO: some host system doesn't set errno
    }
}
#[cfg(feature = "stdio")]
pub(crate) fn is_terminal(fd: BorrowedFd<'_>) -> bool {
    sys_istty(fd).unwrap_or(false)
}

/// [SYS_OPEN (0x01)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-open-0x01)
pub fn sys_open(path: &CStr, mode: OpenMode) -> Result<OwnedFd> {
    let args = [
        ParamRegR::c_str(path),
        ParamRegR::usize(mode as usize),
        ParamRegR::usize(path.to_bytes().len()),
    ];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_OPEN, ParamRegR::block(&args)) };
    match res.raw_fd() {
        Some(fd) => {
            debug_assert_ne!(res.usize(), 0);
            Ok(unsafe { OwnedFd::from_raw_fd(fd) })
        }
        None => Err(Error::from_raw_os_error(sys_errno())),
    }
}
// From https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-open-0x01:
// > ARM targets interpret the special path name `:tt` as meaning the console
// > input stream, for an open-read or the console output stream, for an open-write.
// > Opening these streams is performed as part of the standard startup code for
// > those applications that reference the C `stdio` streams.
// And, if the SH_EXT_STDOUT_STDERR semihosting extension is supported:
// > If the special path name `:tt` is opened with an `fopen` mode requesting write access (`w`, `wb`, `w+`, or `w+b`), then this is a request to open `stdout`.
// > If the special path name `:tt` is opened with a mode requesting append access (`a`, `ab`, `a+`, or `a+b`), then this is a request to open `stderr`.
#[cfg(feature = "stdio")]
pub(crate) type StdioFd = OwnedFd;
#[cfg(feature = "stdio")]
pub(crate) fn stdin() -> Result<StdioFd> {
    sys_open(c!(":tt"), OpenMode::RDONLY)
}
#[cfg(feature = "stdio")]
pub(crate) fn stdout() -> Result<StdioFd> {
    sys_open(c!(":tt"), OpenMode::WRONLY_TRUNC)
}
#[cfg(feature = "stdio")]
pub(crate) fn stderr() -> Result<StdioFd> {
    // if failed, redirect to stdout
    sys_open(c!(":tt"), OpenMode::WRONLY_APPEND).or_else(|_| stdout())
}
#[inline]
pub(crate) fn should_close(_fd: &OwnedFd) -> bool {
    // In Arm semihosting, stdio streams are handled like normal fd.
    true
}

// TODO: Add read_uninit?
/// [SYS_READ (0x06)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-read-0x06)
pub fn sys_read(fd: BorrowedFd<'_>, buf: &mut [MaybeUninit<u8>]) -> Result<usize> {
    let len = buf.len();
    let mut args = [ParamRegW::fd(fd), ParamRegW::buf(buf), ParamRegW::usize(len)];
    let res = unsafe { syscall(OperationNumber::SYS_READ, ParamRegW::block(&mut args)) };
    if res.usize() <= len {
        Ok(len - res.usize())
    } else {
        Err(Error::from_raw_os_error(sys_errno()))
    }
}
#[cfg(any(feature = "stdio", feature = "fs"))]
pub(crate) fn read(fd: BorrowedFd<'_>, buf: &mut [u8]) -> Result<usize> {
    use core::slice;

    let len = buf.len();
    // SAFETY: transmuting initialized u8 to MaybeUninit<u8> is always safe.
    let buf = unsafe { slice::from_raw_parts_mut(buf.as_mut_ptr().cast::<MaybeUninit<u8>>(), len) };
    sys_read(fd, buf)
}

/// [SYS_READC (0x07)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-readc-0x07)
pub fn sys_readc() -> u8 {
    let res = unsafe { syscall0(OperationNumber::SYS_READC) };
    res.u8()
}

/// [SYS_REMOVE (0x0E)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-remove-0x0e)
pub fn sys_remove(path: &CStr) -> Result<()> {
    let args = [ParamRegR::c_str(path), ParamRegR::usize(path.to_bytes().len())];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_REMOVE, ParamRegR::block(&args)) };
    if res.usize() == 0 { Ok(()) } else { Err(Error::from_raw_os_error(sys_errno())) }
}

/// [SYS_RENAME (0x0F)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-rename-0x0f)
pub fn sys_rename(from: &CStr, to: &CStr) -> Result<()> {
    let args = [
        ParamRegR::c_str(from),
        ParamRegR::usize(from.to_bytes().len()),
        ParamRegR::c_str(to),
        ParamRegR::usize(to.to_bytes().len()),
    ];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_RENAME, ParamRegR::block(&args)) };
    if res.usize() == 0 { Ok(()) } else { Err(Error::from_raw_os_error(sys_errno())) }
}

// TODO: resolve safety
// > The effect of seeking outside the current extent of the file object is undefined.
/// [SYS_SEEK (0x0A)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-seek-0x0a)
pub unsafe fn sys_seek(fd: BorrowedFd<'_>, abs_pos: usize) -> Result<()> {
    let args = [ParamRegR::fd(fd), ParamRegR::usize(abs_pos)];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_SEEK, ParamRegR::block(&args)) };
    if res.usize() == 0 { Ok(()) } else { Err(Error::from_raw_os_error(sys_errno())) }
}

/// [SYS_SYSTEM (0x12)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-system-0x12)
pub fn sys_system(cmd: &CStr) -> usize {
    let args = [ParamRegR::c_str(cmd), ParamRegR::usize(cmd.to_bytes().len())];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_SYSTEM, ParamRegR::block(&args)) };
    res.usize()
}

/// [SYS_TICKFREQ (0x31)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-tickfreq-0x31)
pub fn sys_tickfreq() -> Result<usize> {
    let res = unsafe { syscall0(OperationNumber::SYS_TICKFREQ) };
    if res.int() == -1 { Err(Error::from_raw_os_error(sys_errno())) } else { Ok(res.usize()) }
}

/// [SYS_TIME (0x11)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-time-0x11)
#[allow(clippy::unnecessary_wraps)] // TODO: change in next breaking release?
pub fn sys_time() -> Result<usize> {
    let res = unsafe { syscall0(OperationNumber::SYS_TIME) };
    Ok(res.usize())
}

/// [SYS_WRITE (0x05)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-write-0x05)
pub fn sys_write(fd: BorrowedFd<'_>, buf: &[u8]) -> Result<usize> {
    let args = [ParamRegR::fd(fd), ParamRegR::buf(buf), ParamRegR::usize(buf.len())];
    let res = unsafe { syscall_readonly(OperationNumber::SYS_WRITE, ParamRegR::block(&args)) };
    match res.usize() {
        0 => Ok(buf.len()),
        not_written if not_written <= buf.len() => {
            if not_written == buf.len() && !buf.is_empty() {
                // At least on qemu-system-arm 7.2, if fd is a read-only file,
                // this is returned instead of an error.
                return Err(Error::from_raw_os_error(sys_errno()));
            }
            Ok(buf.len() - not_written)
        }
        _ => Err(Error::from_raw_os_error(sys_errno())),
    }
}
#[cfg(any(feature = "stdio", feature = "fs"))]
pub(crate) use self::sys_write as write;

/// [SYS_WRITEC (0x03)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-writec-0x03)
pub fn sys_writec(b: u8) {
    unsafe {
        syscall_readonly(OperationNumber::SYS_WRITEC, ParamRegR::ref_(&b));
    }
}

/// [SYS_WRITE0 (0x04)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-write0-0x04)
pub fn sys_write0(s: &CStr) {
    unsafe {
        syscall_readonly(OperationNumber::SYS_WRITE0, ParamRegR::c_str(s));
    }
}
