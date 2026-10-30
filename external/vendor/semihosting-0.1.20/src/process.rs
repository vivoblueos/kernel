// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A module for working with processes.
//!
//! This module provides [`abort`] and [`exit`] for terminating the current process.
//!
//! See also [`semihosting::sys::arm_compat::sys_system`] for platform-specific
//! semihosting interface to run a system command on the host command-line interpreter.

use core::{convert::Infallible, fmt};

use crate::sys;

/// This type represents the status code the current process can return
/// to its parent under normal termination.
#[derive(Debug, Clone, Copy)]
pub struct ExitCode(u8);

impl ExitCode {
    /// The canonical `ExitCode` for successful termination on this platform.
    pub const SUCCESS: Self = Self(0);

    /// The canonical `ExitCode` for unsuccessful termination on this platform.
    pub const FAILURE: Self = Self(1);

    // Note: the corresponding API in std is still unstable: https://github.com/rust-lang/rust/issues/97100
    /// Exit the current process with the given `ExitCode`.
    ///
    /// Note that this has the same caveats as [`process::exit()`][exit], namely that this function
    /// terminates the process immediately, so no destructors on the current stack or any other
    /// thread's stack will be run.
    pub fn exit_process(self) -> ! {
        exit(self.0 as i32)
    }
}

/// The default value is [`ExitCode::SUCCESS`]
impl Default for ExitCode {
    fn default() -> Self {
        Self::SUCCESS
    }
}

impl From<u8> for ExitCode {
    /// Constructs an `ExitCode` from an arbitrary u8 value.
    fn from(code: u8) -> Self {
        Self(code)
    }
}

/// Terminates the current process with the specified exit code.
///
/// Note that because this function never returns, and that it terminates the
/// process, no destructors on the current stack or any other thread's stack
/// will be run.
pub fn exit(code: i32) -> ! {
    sys::exit(code);
    #[allow(clippy::empty_loop)] // this crate is #![no_std]
    loop {}
}

/// Terminates the process in an abnormal fashion.
///
/// Note that because this function never returns, and that it terminates the
/// process, no destructors on the current stack or any other thread's stack
/// will be run.
#[cold]
pub fn abort() -> ! {
    exit(134) // SIGABRT
}

/// A trait for implementing arbitrary return types in the `main` function.
pub trait Termination {
    /// Is called to get the representation of the value as status code.
    /// This status code is returned to the operating system.
    fn report(self) -> ExitCode;
}

impl Termination for () {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::SUCCESS
    }
}

// TODO: ! type is unstable: https://github.com/rust-lang/rust/issues/35121
// impl Termination for ! {
//     fn report(self) -> ExitCode {
//         self
//     }
// }

impl Termination for Infallible {
    fn report(self) -> ExitCode {
        match self {}
    }
}

impl Termination for ExitCode {
    #[inline]
    fn report(self) -> ExitCode {
        self
    }
}

impl<T: Termination, E: fmt::Debug> Termination for Result<T, E> {
    #[allow(clippy::used_underscore_binding)]
    fn report(self) -> ExitCode {
        match self {
            Ok(val) => val.report(),
            Err(_err) => {
                #[cfg(feature = "stdio")]
                eprintln!("Error: {_err:?}");
                ExitCode::FAILURE
            }
        }
    }
}
