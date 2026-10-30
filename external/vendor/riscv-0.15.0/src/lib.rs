//! Low level access to RISC-V processors
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.60 and up. It *might*
//! compile with older versions but that may change in any new patch release.
//!
//! # Features
//!
//! This crate provides:
//!
//! - Access to core registers like `mstatus` or `mcause`.
//! - Interrupt manipulation mechanisms.
//! - Wrappers around assembly instructions like `WFI`.
//!
//! # Optional features
//!
//! ## `s-mode`
//!
//! This feature re-exports in `interrupt` S-mode interrupt functions defined in `interrupt::supervisor`.
//! By default, the crate assumes that the target is running in M-mode.
//! Thus, `interrupt` re-exports the M-mode functions defined in `interrupt::machine`.
//!
//! ## `critical-section-single-hart`
//!
//! This feature enables a [`critical-section`](https://github.com/rust-embedded/critical-section)
//! implementation suitable for single-hart targets, based on disabling interrupts globally.
//! This feature uses S-mode interrupt handling if the `s-mode` feature is enabled, and M-mode otherwise.
//!
//! It is **unsound** to enable it on multi-hart targets,
//! and may cause functional problems in systems where some interrupts must NOT be disabled
//! or critical sections are managed as part of an RTOS. In these cases, you should use
//! a target-specific implementation instead, typically provided by a HAL or RTOS crate.

#![no_std]
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::eq_op)]
#![allow(clippy::identity_op)]

pub use paste::paste;

pub mod asm;
pub mod bits;
pub mod delay;
pub mod interrupt;
pub mod register;

// Re-export crates of the RISC-V ecosystem
#[cfg(feature = "riscv-macros")]
pub use riscv_macros::*;
pub use riscv_pac::*;

#[macro_use]
mod macros;

#[cfg(all(
    any(target_arch = "riscv32", target_arch = "riscv64"),
    feature = "critical-section-single-hart"
))]
mod critical_section;

/// Used to reexport items for use in macros. Do not use directly.
/// Not covered by semver guarantees.
#[doc(hidden)]
pub mod _export {
    pub use critical_section;
}
