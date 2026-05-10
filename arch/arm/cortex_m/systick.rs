// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Cortex-M SysTick timer registers.
//!
//! This register block follows Arm CMSIS-Core's `SysTick_Type` layout:
//! <https://arm-software.github.io/CMSIS_6/latest/Core/structSysTick__Type.html>
//!
//! The CMSIS layout defines the control/status, reload, current value, and
//! calibration registers for the Cortex-M system timer.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_structs,
    registers::{ReadOnly, ReadWrite},
};

const SYSTICK_BASE: usize = 0xE000_E010;
const CSR_ENABLE: u32 = 1 << 0;
const CSR_TICKINT: u32 = 1 << 1;
const CSR_CLKSOURCE: u32 = 1 << 2;
const CSR_COUNTFLAG: u32 = 1 << 16;

#[inline(always)]
fn registers() -> &'static SystickRegisters {
    // Safety: SysTick is a core peripheral at a fixed architectural MMIO address.
    unsafe { &*(SYSTICK_BASE as *const SystickRegisters) }
}

/// Disables the SysTick counter.
///
/// # Safety
///
/// The caller must ensure this does not violate timer or scheduler invariants.
#[inline(always)]
pub unsafe fn disable_counter() {
    let csr = registers().CSR.get() & !CSR_ENABLE;
    registers().CSR.set(csr);
}

/// Selects the core clock as the SysTick clock source.
///
/// # Safety
///
/// The caller must ensure the selected clock source is valid for the board.
#[inline(always)]
pub unsafe fn use_core_clock() {
    let csr = registers().CSR.get() | CSR_CLKSOURCE;
    registers().CSR.set(csr);
}

/// Sets the SysTick reload value.
///
/// # Safety
///
/// The caller must pass a valid 24-bit SysTick reload value.
#[inline(always)]
pub unsafe fn set_reload(value: u32) {
    registers().RVR.set(value);
}

/// Clears the SysTick current value and COUNTFLAG.
///
/// # Safety
///
/// The caller must account for the side effect of clearing COUNTFLAG.
#[inline(always)]
pub unsafe fn clear_current() {
    registers().CVR.set(0);
}

/// Enables the SysTick counter.
///
/// # Safety
///
/// The caller must ensure reload/current/control have been initialized.
#[inline(always)]
pub unsafe fn enable_counter() {
    let csr = registers().CSR.get() | CSR_ENABLE;
    registers().CSR.set(csr);
}

/// Enables SysTick interrupts.
///
/// # Safety
///
/// The caller must ensure the SysTick handler is installed and has a valid
/// priority before enabling the interrupt.
#[inline(always)]
pub unsafe fn enable_interrupt() {
    let csr = registers().CSR.get() | CSR_TICKINT;
    registers().CSR.set(csr);
}

/// Returns whether SysTick has wrapped since the last CSR read.
///
/// # Safety
///
/// Reading CSR clears COUNTFLAG, so the caller must account for that side
/// effect.
#[inline(always)]
pub unsafe fn has_wrapped() -> bool {
    (registers().CSR.get() & CSR_COUNTFLAG) != 0
}

register_structs! {
    /// SysTick register block.
    #[allow(non_snake_case)]
    SystickRegisters {
        /// Control and Status Register.
        (0x000 => CSR: ReadWrite<u32>),
        /// Reload Value Register.
        (0x004 => RVR: ReadWrite<u32>),
        /// Current Value Register.
        (0x008 => CVR: ReadWrite<u32>),
        /// Calibration Value Register.
        (0x00C => CALIB: ReadOnly<u32>),
        (0x010 => @END),
    }
}
