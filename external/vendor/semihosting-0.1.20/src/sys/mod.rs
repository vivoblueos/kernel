// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Low-level access to platform-specific semihosting interfaces.

#![allow(
    missing_docs,
    non_camel_case_types,
    non_upper_case_globals,
    clippy::unnecessary_wraps,
    clippy::upper_case_acronyms
)]

#[cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv32",
    target_arch = "riscv64",
    all(target_arch = "xtensa", feature = "openocd-semihosting"),
))]
use self::arm_compat as arch;
#[cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv32",
    target_arch = "riscv64",
    all(target_arch = "xtensa", feature = "openocd-semihosting"),
))]
#[cfg_attr(
    docsrs,
    doc(cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        all(target_arch = "xtensa", feature = "openocd-semihosting"),
    )))
)]
pub mod arm_compat;

#[cfg(any(
    target_arch = "mips",
    target_arch = "mips32r6",
    target_arch = "mips64",
    target_arch = "mips64r6",
))]
use self::mips as arch;
#[cfg(any(
    all(doc, docsrs),
    target_arch = "mips",
    target_arch = "mips32r6",
    target_arch = "mips64",
    target_arch = "mips64r6",
))]
#[cfg_attr(
    docsrs,
    doc(cfg(any(
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
    )))
)]
pub mod mips;

mod errno;
mod reg;

#[cfg(feature = "fs")]
pub(crate) use self::arch::fs;
#[cfg(feature = "stdio")]
pub(crate) use self::arch::{StdioFd, is_terminal, stderr, stdin, stdout};
#[cfg(any(feature = "stdio", feature = "fs"))]
pub(crate) use self::arch::{read, write};
pub(crate) use self::{
    arch::{close, exit, should_close},
    errno::{decode_error_kind, is_interrupted},
};
