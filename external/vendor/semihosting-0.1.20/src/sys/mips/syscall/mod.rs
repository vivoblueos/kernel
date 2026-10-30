// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Raw semihosting call.

pub use self::arch::{
    syscall0, syscall1, syscall1_readonly, syscall2, syscall2_readonly, syscall3,
    syscall3_readonly, syscall4, syscall4_readonly,
};
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    any(
        doc,
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
    ),
    path = "mips.rs"
)]
mod arch;

pub use crate::sys::reg::{ParamRegR, ParamRegW, RetReg};

/// Semihosting operation code.
#[derive(Debug, Clone, Copy)]
pub struct OperationCode(usize);
impl OperationCode {
    pub const UHI_EXIT: Self = Self(1);
    pub const UHI_OPEN: Self = Self(2);
    pub const UHI_CLOSE: Self = Self(3);
    pub const UHI_READ: Self = Self(4);
    pub const UHI_WRITE: Self = Self(5);
    pub const UHI_LSEEK: Self = Self(6);
    pub const UHI_UNLINK: Self = Self(7);
    pub const UHI_FSTAT: Self = Self(8);
    pub const UHI_ARGC: Self = Self(9);
    pub const UHI_ARGNLEN: Self = Self(10);
    pub const UHI_ARGN: Self = Self(11);
    // const UHI_RAMRANGE : Self = Self(12); // QEMU (as of 7.2) doesn't support this
    // const UHI_PLOG : Self = Self(13); // TODO
    // const UHI_ASSERT : Self = Self(14); // TODO
    // const UHI_EXCEPTION : Self = Self(15); // QEMU (as of 7.2) doesn't support this
    pub const UHI_PREAD: Self = Self(19);
    pub const UHI_PWRITE: Self = Self(20);
    pub const UHI_LINK: Self = Self(22);
    // const UHI_BOOT_FAIL : Self = Self(23); // QEMU (as of 7.2) doesn't support this
}
