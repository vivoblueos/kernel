//! Processor core registers
//!
//! The following registers can only be accessed in PRIVILEGED mode:
//!
//! - BASEPRI
//! - CONTROL
//! - FAULTMASK
//! - MSP
//! - PRIMASK
//!
//! The rest of registers (see list below) can be accessed in either, PRIVILEGED
//! or UNPRIVILEGED, mode.
//!
//! - APSR
//! - LR
//! - PC
//! - PSP
//!
//! The following registers are NOT available on ARMv6-M devices
//! (`thumbv6m-none-eabi`):
//!
//! - BASEPRI
//! - FAULTMASK
//!
//! The following registers are only available for devices with an FPU:
//!
//! - FPSCR
//!
//! # References
//!
//! - Cortex-M* Devices Generic User Guide - Section 2.1.3 Core registers

#[cfg(all(not(armv6m), not(armv8m_base)))]
pub mod basepri;

#[cfg(all(not(armv6m), not(armv8m_base)))]
pub mod basepri_max;

pub mod control;

#[cfg(all(not(armv6m), not(armv8m_base)))]
pub mod faultmask;

#[cfg(has_fpu)]
pub mod fpscr;

pub mod msp;

pub mod primask;

pub mod psp;

#[cfg(armv8m_main)]
pub mod msplim;

#[cfg(armv8m_main)]
pub mod psplim;

// Accessing these registers requires inline assembly because their contents are tied to the current
// stack frame
#[cfg(feature = "inline-asm")]
pub mod apsr;

#[cfg(feature = "inline-asm")]
pub mod lr;

#[cfg(feature = "inline-asm")]
pub mod pc;
