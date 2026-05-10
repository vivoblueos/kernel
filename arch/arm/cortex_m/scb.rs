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

//! Cortex-M System Control Block (SCB) registers.
//!
//! This register block follows Arm CMSIS-Core's `SCB_Type` layout:
//! <https://arm-software.github.io/CMSIS_6/v6.0.0/Core/structSCB__Type.html>
//!
//! The CMSIS layout describes the interrupt-control register, system handler
//! priority bytes, system fault status registers, and coprocessor control
//! register used by Cortex-M system control code.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_structs,
    registers::ReadWrite,
};

const SCB_BASE: usize = 0xE000_ED04;
const ICSR_VECTACTIVE_MASK: u32 = 0x1ff;
const ICSR_PENDSVSET: u32 = 1 << 28;
const ICSR_PENDSTSET: u32 = 1 << 26;
const SHCSR_MEMFAULTENA: u32 = 1 << 16;

/// System handlers with configurable priority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum SystemHandler {
    /// SVCall exception.
    SVCall = 11,
    /// PendSV exception.
    PendSV = 14,
    /// SysTick exception.
    SysTick = 15,
}

/// Snapshot of SCB fault status registers.
#[derive(Debug, Default, Clone, Copy)]
pub struct FaultStatus {
    /// Configurable Fault Status Register.
    pub cfsr: u32,
    /// HardFault Status Register.
    pub hfsr: u32,
    /// Memory Management Fault Address Register.
    pub mmfar: u32,
    /// BusFault Address Register.
    pub bfar: u32,
    /// Auxiliary Fault Status Register.
    pub afsr: u32,
}

#[inline(always)]
fn registers() -> &'static ScbRegisters {
    // Safety: SCB is a core peripheral at a fixed architectural MMIO address.
    unsafe { &*(SCB_BASE as *const ScbRegisters) }
}

/// Sets the PendSV pending bit.
///
/// # Safety
///
/// The caller must ensure that pending PendSV is valid in the current kernel
/// state and will not violate priority- or interrupt-based invariants.
#[inline(always)]
pub unsafe fn set_pendsv() {
    registers().ICSR.set(ICSR_PENDSVSET);
}

/// Sets the SysTick pending bit.
///
/// # Safety
///
/// The caller must ensure that pending SysTick is valid in the current kernel
/// state and that the SysTick handler is installed.
#[inline(always)]
pub unsafe fn set_pendst() {
    registers().ICSR.set(ICSR_PENDSTSET);
}

/// Returns the raw active exception number from ICSR.VECTACTIVE.
///
/// # Safety
///
/// The caller must run on a Cortex-M profile where this SCB register block is
/// present at the architectural address.
#[inline(always)]
pub unsafe fn active_exception_number() -> u16 {
    (registers().ICSR.get() & ICSR_VECTACTIVE_MASK) as u16
}

/// Returns whether the CPU is currently handling an exception.
///
/// # Safety
///
/// The caller must run on a Cortex-M profile where this SCB register block is
/// present at the architectural address.
#[inline(always)]
pub unsafe fn is_in_exception() -> bool {
    unsafe { active_exception_number() != 0 }
}

/// Sets the encoded priority byte for a configurable system handler.
///
/// # Safety
///
/// Changing priorities can invalidate priority-based critical sections if the
/// caller does not preserve the kernel's priority invariants.
#[inline(always)]
pub unsafe fn set_system_handler_priority(handler: SystemHandler, priority: u8) {
    // Cortex-M SHPR byte 0 maps to exception 4. This mirrors the previous
    // cortex-m crate call for the supported ARMv7-M/ARMv8-M targets.
    let index = handler as usize - 4;

    // Safety: SystemHandler values are all in the configurable [4, 15] range.
    unsafe {
        registers().SHPR.get_unchecked(index).set(priority);
    }
}

/// Reads the SCB fault status registers.
///
/// # Safety
///
/// The caller must run on a Cortex-M profile that implements these fault
/// status registers at the architectural SCB offsets.
#[inline(always)]
pub unsafe fn read_fault_status() -> FaultStatus {
    let regs = registers();
    FaultStatus {
        cfsr: regs.CFSR.get(),
        hfsr: regs.HFSR.get(),
        mmfar: regs.MMFAR.get(),
        bfar: regs.BFAR.get(),
        afsr: regs.AFSR.get(),
    }
}

/// Reads the Configurable Fault Status Register.
///
/// # Safety
///
/// The caller must run on a Cortex-M profile that implements CFSR.
#[inline(always)]
pub unsafe fn cfsr() -> u32 {
    registers().CFSR.get()
}

/// Writes the Configurable Fault Status Register.
///
/// # Safety
///
/// The caller must write only architecturally valid write-one-to-clear fault
/// status bits for the current handler state.
#[inline(always)]
pub unsafe fn write_cfsr(value: u32) {
    registers().CFSR.set(value);
}

/// Enables MemManage faults in SHCSR.
///
/// # Safety
///
/// The caller must ensure that the MemManage handler is installed before
/// enabling MemManage faults.
#[inline(always)]
pub unsafe fn enable_memfault() {
    let shcsr = registers().SHCSR.get() | SHCSR_MEMFAULTENA;
    registers().SHCSR.set(shcsr);
}

register_structs! {
    /// System Control Block register block.
    #[allow(non_snake_case)]
    ScbRegisters {
        /// Interrupt Control and State Register.
        (0x000 => ICSR: ReadWrite<u32>),
        /// Vector Table Offset Register.
        (0x004 => VTOR: ReadWrite<u32>),
        /// Application Interrupt and Reset Control Register.
        (0x008 => AIRCR: ReadWrite<u32>),
        /// System Control Register.
        (0x00C => SCR: ReadWrite<u32>),
        /// Configuration and Control Register.
        (0x010 => CCR: ReadWrite<u32>),
        /// System Handler Priority Registers, byte-addressable on ARMv7-M/ARMv8-M.
        (0x014 => SHPR: [ReadWrite<u8>; 12]),
        /// System Handler Control and State Register.
        (0x020 => SHCSR: ReadWrite<u32>),
        /// Configurable Fault Status Register.
        (0x024 => CFSR: ReadWrite<u32>),
        /// HardFault Status Register.
        (0x028 => HFSR: ReadWrite<u32>),
        /// Debug Fault Status Register.
        (0x02C => DFSR: ReadWrite<u32>),
        /// Memory Management Fault Address Register.
        (0x030 => MMFAR: ReadWrite<u32>),
        /// BusFault Address Register.
        (0x034 => BFAR: ReadWrite<u32>),
        /// Auxiliary Fault Status Register.
        (0x038 => AFSR: ReadWrite<u32>),
        (0x03C => _reserved0),
        /// Coprocessor Access Control Register.
        (0x084 => CPACR: ReadWrite<u32>),
        (0x088 => @END),
    }
}
