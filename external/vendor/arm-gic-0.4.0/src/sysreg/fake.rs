// Copyright 2025 The arm-gic Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

//! Fake implementations of system register getters and setters for unit tests.

use std::sync::Mutex;

/// Values of fake system registers.
pub static SYSREGS: Mutex<SystemRegisters> = Mutex::new(SystemRegisters::new());

/// A set of fake system registers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SystemRegisters {
    pub icc_iar1_el1: u32,
    pub icc_ctlr_el1: u32,
    pub icc_eoir1_el1: u32,
    pub icc_igrpen0_el1: u32,
    pub icc_igrpen1_el1: u32,
    pub icc_pmr_el1: u32,
    pub icc_sgi1r_el1: u64,
    pub icc_sre_el1: u32,
}

impl SystemRegisters {
    const fn new() -> Self {
        Self {
            icc_iar1_el1: 0,
            icc_ctlr_el1: 0,
            icc_eoir1_el1: 0,
            icc_igrpen0_el1: 0,
            icc_igrpen1_el1: 0,
            icc_pmr_el1: 0,
            icc_sgi1r_el1: 0,
            icc_sre_el1: 0,
        }
    }
}

/// Generates a public function named `$function_name` to read the fake system register `$sysreg`.
macro_rules! read_sysreg32 {
    ($sysreg:ident, $opc1:literal, $crm:ident, $crn:ident, $opc2: literal, $function_name:ident) => {
        pub fn $function_name() -> u32 {
            crate::sysreg::fake::SYSREGS.lock().unwrap().$sysreg
        }
    };
}

/// Generates a public function named `$function_name` to write to the fake system register
/// `$sysreg`.
macro_rules! write_sysreg32 {
    ($sysreg:ident, $opc1:literal, $crm:ident, $crn:ident, $opc2: literal, $function_name:ident) => {
        pub fn $function_name(value: u32) {
            crate::sysreg::fake::SYSREGS.lock().unwrap().$sysreg = value;
        }
    };
}

/// Generates a public function named `$function_name` to write to the fake system register
/// `$sysreg`.
macro_rules! write_sysreg64 {
    ($sysreg:ident, $opc1:literal, $crm:ident, $function_name:ident) => {
        pub fn $function_name(value: u64) {
            crate::sysreg::fake::SYSREGS.lock().unwrap().$sysreg = value;
        }
    };
}
