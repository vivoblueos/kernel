// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Raw semihosting call.

pub use self::arch::{syscall, syscall_readonly};
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(target_arch = "aarch64", path = "aarch64.rs")]
#[cfg_attr(target_arch = "arm", path = "arm.rs")]
#[cfg_attr(any(target_arch = "riscv32", target_arch = "riscv64"), path = "riscv.rs")]
#[cfg_attr(target_arch = "xtensa", path = "xtensa.rs")]
mod arch;

pub use crate::sys::reg::{ParamRegR, ParamRegW, RetReg};

/// Semihosting operation numbers.
///
/// - `0x00-0x31` Used by Arm.
/// - `0x32-0xFF` Reserved for future use by Arm.
/// - `0x100-0x1FF` Reserved for user applications.
/// - `0x200-0xFFFFFFFF` Undefined and currently unused.
#[derive(Debug, Copy, Clone)]
pub struct OperationNumber(u32);
impl OperationNumber {
    /// [SYS_OPEN (0x01)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-open-0x01)
    pub const SYS_OPEN: Self = Self(0x01);
    /// [SYS_CLOSE (0x02)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-close-0x02)
    pub const SYS_CLOSE: Self = Self(0x02);
    /// [SYS_WRITEC (0x03)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-writec-0x03)
    pub const SYS_WRITEC: Self = Self(0x03);
    /// [SYS_WRITE0 (0x04)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-write0-0x04)
    pub const SYS_WRITE0: Self = Self(0x04);
    /// [SYS_WRITE (0x05)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-write-0x05)
    pub const SYS_WRITE: Self = Self(0x05);
    /// [SYS_READ (0x06)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-read-0x06)
    pub const SYS_READ: Self = Self(0x06);
    /// [SYS_READC (0x07)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-readc-0x07)
    pub const SYS_READC: Self = Self(0x07);
    /// [SYS_ISERROR (0x08)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-iserror-0x08)
    pub const SYS_ISERROR: Self = Self(0x08);
    /// [SYS_ISTTY (0x09)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-istty-0x09)
    pub const SYS_ISTTY: Self = Self(0x09);
    /// [SYS_SEEK (0x0A)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-seek-0x0a)
    pub const SYS_SEEK: Self = Self(0x0A);
    /// [SYS_FLEN (0x0C)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-flen-0x0c)
    pub const SYS_FLEN: Self = Self(0x0C);
    // /// [SYS_TMPNAM (0x0D)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-tmpnam-0x0d)
    // #[deprecated = "tmpnam is deprecated as not secure on most host systems"]
    //  pub const SYS_TMPNAM : Self = Self(0x0D);
    /// [SYS_REMOVE (0x0E)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-remove-0x0e)
    pub const SYS_REMOVE: Self = Self(0x0E);
    /// [SYS_RENAME (0x0F)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-rename-0x0f)
    pub const SYS_RENAME: Self = Self(0x0F);
    /// [SYS_CLOCK (0x10)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-clock-0x10)
    pub const SYS_CLOCK: Self = Self(0x10);
    /// [SYS_TIME (0x11)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-time-0x11)
    pub const SYS_TIME: Self = Self(0x11);
    /// [SYS_SYSTEM (0x12)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-system-0x12)
    pub const SYS_SYSTEM: Self = Self(0x12);
    /// [SYS_ERRNO (0x13)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-errno-0x13)
    pub const SYS_ERRNO: Self = Self(0x13);
    /// [SYS_GET_CMDLINE (0x15)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-get_cmdline-0x15)
    pub const SYS_GET_CMDLINE: Self = Self(0x15);
    /// [SYS_HEAPINFO (0x16)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-heapinfo-0x16)
    pub const SYS_HEAPINFO: Self = Self(0x16);
    // #[deprecated = "obsoleted in semihosting specification version 2.0"]
    //  pub const angel_SWIreason_EnterSVC : Self = Self(0x17);
    /// [SYS_EXIT (0x18)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-exit-0x18)
    #[doc(alias = "angel_SWIreason_ReportException")] // old name
    pub const SYS_EXIT: Self = Self(0x18);
    // #[deprecated = "obsoleted in semihosting specification version 2.0"]
    //  pub const angelSWI_Reason_SyncCacheRange : Self = Self(0x19);
    /// [SYS_EXIT_EXTENDED (0x20)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-exit_extended-0x20)
    pub const SYS_EXIT_EXTENDED: Self = Self(0x20);
    /// [SYS_ELAPSED (0x30)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-elapsed-0x30)
    pub const SYS_ELAPSED: Self = Self(0x30);
    /// [SYS_TICKFREQ (0x31)](https://github.com/ARM-software/abi-aa/blob/2024Q3/semihosting/semihosting.rst#sys-tickfreq-0x31)
    pub const SYS_TICKFREQ: Self = Self(0x31);

    #[inline] // inline to help compiler to remove assertion
    pub const fn user_defined(number: u32) -> Self {
        assert!(number >= 0x100 && number <= 0x1FF);
        Self(number)
    }
}

/// `syscall_readonly(number, null)`
#[inline]
pub unsafe fn syscall0(number: OperationNumber) -> RetReg {
    // In most operations that don't have parameters, such as SYS_ERRNO, and
    // SYS_CLOCK, the PARAMETER REGISTER must be zero.
    unsafe { syscall_readonly(number, ParamRegR::usize(0)) }
}
