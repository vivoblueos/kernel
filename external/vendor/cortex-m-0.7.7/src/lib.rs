//! Low level access to Cortex-M processors
//!
//! This crate provides:
//!
//! - Access to core peripherals like NVIC, SCB and SysTick.
//! - Access to core registers like CONTROL, MSP and PSR.
//! - Interrupt manipulation mechanisms
//! - Safe wrappers around Cortex-M specific instructions like `bkpt`
//!
//! # Optional features
//!
//! ## `inline-asm`
//!
//! When this feature is enabled the implementation of all the functions inside the `asm` and
//! `register` modules use inline assembly (`asm!`) instead of external assembly (FFI into separate
//! assembly files pre-compiled using `arm-none-eabi-gcc`). The advantages of enabling `inline-asm`
//! are:
//!
//! - Reduced overhead. FFI eliminates the possibility of inlining so all operations include a
//! function call overhead when `inline-asm` is not enabled.
//!
//! - Some of the `register` API only becomes available only when `inline-asm` is enabled. Check the
//! API docs for details.
//!
//! The disadvantage is that `inline-asm` requires a Rust version at least 1.59 to use the `asm!()`
//! macro. In the future 0.8 and above versions of `cortex-m`, this feature will always be enabled.
//!
//! ## `critical-section-single-core`
//!
//! This feature enables a [`critical-section`](https://github.com/rust-embedded/critical-section)
//! implementation suitable for single-core targets, based on disabling interrupts globally.
//!
//! It is **unsound** to enable it on multi-core targets or for code running in unprivileged mode,
//! and may cause functional problems in systems where some interrupts must be not be disabled
//! or critical sections are managed as part of an RTOS. In these cases, you should use
//! a target-specific implementation instead, typically provided by a HAL or RTOS crate.
//!
//! ## `cm7-r0p1`
//!
//! This feature enables workarounds for errata found on Cortex-M7 chips with revision r0p1. Some
//! functions in this crate only work correctly on those chips if this Cargo feature is enabled
//! (the functions are documented accordingly).
//!
//! ## `linker-plugin-lto`
//!
//! This feature links against prebuilt assembly blobs that are compatible with [Linker-Plugin LTO].
//! This allows inlining assembly routines into the caller, even without the `inline-asm` feature,
//! and works on stable Rust (but note the drawbacks below!).
//!
//! If you want to use this feature, you need to be aware of a few things:
//!
//! - You need to make sure that `-Clinker-plugin-lto` is passed to rustc. Please refer to the
//!   [Linker-Plugin LTO] documentation for details.
//!
//! - You have to use a Rust version whose LLVM version is compatible with the toolchain in
//!   `asm-toolchain`.
//!
//! - Due to a [Rust bug][rust-lang/rust#75940] in compiler versions **before 1.49**, this option
//!   does not work with optimization levels `s` and `z`.
//!
//! [Linker-Plugin LTO]: https://doc.rust-lang.org/stable/rustc/linker-plugin-lto.html
//! [rust-lang/rust#75940]: https://github.com/rust-lang/rust/issues/75940
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.38 and up. It *might*
//! compile with older versions but that may change in any new patch release.

#![deny(missing_docs)]
#![no_std]
#![allow(clippy::identity_op)]
#![allow(clippy::missing_safety_doc)]
// Prevent clippy from complaining about empty match expression that are used for cfg gating.
#![allow(clippy::match_single_binding)]
// This makes clippy warn about public functions which are not #[inline].
//
// Almost all functions in this crate result in trivial or even no assembly.
// These functions should be #[inline].
//
// If you do add a function that's not supposed to be #[inline], you can add
// #[allow(clippy::missing_inline_in_public_items)] in front of it to add an
// exception to clippy's rules.
//
// This should be done in case of:
//  - A function containing non-trivial logic (such as itm::write_all); or
//  - A generated #[derive(Debug)] function (in which case the attribute needs
//    to be applied to the struct).
#![deny(clippy::missing_inline_in_public_items)]
// Don't warn about feature(asm) being stable on Rust >= 1.59.0
#![allow(stable_features)]

extern crate bare_metal;
extern crate volatile_register;

#[macro_use]
mod call_asm;
#[macro_use]
mod macros;

pub mod asm;
#[cfg(armv8m)]
pub mod cmse;
mod critical_section;
pub mod delay;
pub mod interrupt;
#[cfg(all(not(armv6m), not(armv8m_base)))]
pub mod itm;
pub mod peripheral;
pub mod prelude;
pub mod register;

pub use crate::peripheral::Peripherals;
