// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

//! Low level access to processors using the AArch64 execution state.
//!
//! ## Usage
//!
//! Please note that for using this crate's [register definitions](src/registers) (as provided by
//! `aarch64_cpu::registers::*`), you need to also import [`Readable`](registers::Readable) and
//! [`Writeable`](registers::Writeable).
//!
//! ### Example
//!
//! Check out https://github.com/rust-embedded/rust-raspberrypi-OS-tutorials for usage examples.
//! Listed below is a snippet of `rust-raspberrypi-OS-tutorials`'s early boot code.
//!
//! ```rust
//! use aarch64_cpu::{asm, registers::*};
//!
//! // Some parts omitted for brevity.
//!
//! unsafe fn prepare_el2_to_el1_transition(
//!     virt_boot_core_stack_end_exclusive_addr: u64,
//!     virt_kernel_init_addr: u64,
//! ) {
//!     // Enable timer counter registers for EL1.
//!     CNTHCTL_EL2.write(CNTHCTL_EL2::EL1PCEN::SET + CNTHCTL_EL2::EL1PCTEN::SET);
//!
//!     // No offset for reading the counters.
//!     CNTVOFF_EL2.set(0);
//!
//!     // Set EL1 execution state to AArch64.
//!     HCR_EL2.write(HCR_EL2::RW::EL1IsAarch64);
//!
//!     // Set up a simulated exception return.
//!     SPSR_EL2.write(
//!         SPSR_EL2::D::Masked
//!             + SPSR_EL2::A::Masked
//!             + SPSR_EL2::I::Masked
//!             + SPSR_EL2::F::Masked
//!             + SPSR_EL2::M::EL1h,
//!     );
//! }
//! ```
//!
//! ## Disclaimer
//!
//! Descriptive comments in the source files are taken from the [ARM Architecture Reference Manual
//! ARMv8, for ARMv8-A architecture
//! profile](https://static.docs.arm.com/ddi0487/ca/DDI0487C_a_armv8_arm.pdf?_ga=2.266626254.1122218691.1534883460-1326731866.1530967873).

#![no_std]

pub mod asm;
pub mod registers;
