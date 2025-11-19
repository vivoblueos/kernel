// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

#![allow(non_upper_case_globals)]
use crate::arch::irq::IrqNumber;
use core::ffi::CStr;

// Use some names from arm cmsdk.
pub const NONSEC_WATCHDOG_RESET_REQ_IRQn: IrqNumber = IrqNumber::new(0); // Non-Secure Watchdog Reset Request Interrupt
pub const NONSEC_WATCHDOG_IRQn: IrqNumber = IrqNumber::new(1); // Non-Secure Watchdog Interrupt
pub const SLOWCLK_TIMER_IRQn: IrqNumber = IrqNumber::new(2); // SLOWCLK Timer Interrupt
pub const TIMER0_IRQn: IrqNumber = IrqNumber::new(3); // TIMER 0 Interrupt
pub const TIMER1_IRQn: IrqNumber = IrqNumber::new(4); // TIMER 1 Interrupt
pub const TIMER2_IRQn: IrqNumber = IrqNumber::new(5); // TIMER 2 Interrupt
pub const MPC_IRQn: IrqNumber = IrqNumber::new(9); // MPC Combined (Secure) Interrupt
pub const PPC_IRQn: IrqNumber = IrqNumber::new(10); // PPC Combined (Secure) Interrupt
pub const MSC_IRQn: IrqNumber = IrqNumber::new(11); // MSC Combined (Secure) Interrput
pub const BRIDGE_ERROR_IRQn: IrqNumber = IrqNumber::new(12); // Bridge Error Combined (Secure) Interrupt
pub const MGMT_PPU_IRQn: IrqNumber = IrqNumber::new(14); // MGMT PPU
pub const SYS_PPU_IRQn: IrqNumber = IrqNumber::new(15); // SYS PPU
pub const CPU0_PPU_IRQn: IrqNumber = IrqNumber::new(16); // CPU0 PPU
pub const DEBUG_PPU_IRQn: IrqNumber = IrqNumber::new(26); // DEBUG PPU
pub const TIMER3_AON_IRQn: IrqNumber = IrqNumber::new(27); // TIMER 3 AON Interrupt
pub const CPU0_CTI_0_IRQn: IrqNumber = IrqNumber::new(28); // CPU0 CTI IRQ 0
pub const CPU0_CTI_1_IRQn: IrqNumber = IrqNumber::new(29); // CPU0 CTI IRQ 1
pub const System_Timestamp_Counter_IRQn: IrqNumber = IrqNumber::new(32); // System timestamp counter Interrupt

// In the new version of QEMU (9.20), the UART RX interrupt and TX interrupt have been swapped.
// For details, see `fix RX/TX interrupts order <https://github.com/qemu/qemu/commit/5a558be93ad628e5bed6e0ee062870f49251725c>`_
// default set as new version of QEMU
pub const UART0RX_IRQn: IrqNumber = IrqNumber::new(33); // UART 0 TX Interrupt
pub const UART0RX_IRQ_N: u32 = 33;
pub const UART0TX_IRQn: IrqNumber = IrqNumber::new(34); // UART 0 RX Interrupt
pub const UART0TX_IRQ_N: u32 = 34;
pub const UART1RX_IRQn: IrqNumber = IrqNumber::new(35); // UART 1 RX Interrupt
pub const UART1TX_IRQn: IrqNumber = IrqNumber::new(36); // UART 1 TX Interrupt
pub const UART2RX_IRQn: IrqNumber = IrqNumber::new(37); // UART 2 RX Interrupt
pub const UART2TX_IRQn: IrqNumber = IrqNumber::new(38); // UART 2 TX Interrupt
pub const UART3RX_IRQn: IrqNumber = IrqNumber::new(39); // UART 3 RX Interrupt
pub const UART3TX_IRQn: IrqNumber = IrqNumber::new(40); // UART 3 TX Interrupt
pub const UART4RX_IRQn: IrqNumber = IrqNumber::new(41); // UART 4 RX Interrupt
pub const UART4TX_IRQn: IrqNumber = IrqNumber::new(42); // UART 4 TX Interrupt

pub mod memory_map {
    // Secure Subsystem peripheral region
    pub const SYSTIMER0_ARMV8_M_BASE_S: u32 = 0x58000000;
    pub const SYSTIMER1_ARMV8_M_BASE_S: u32 = 0x58001000;
    pub const SYSTIMER2_ARMV8_M_BASE_S: u32 = 0x58002000;
    pub const SYSTIMER3_ARMV8_M_BASE_S: u32 = 0x58003000;
    pub const SLOWCLK_WDOG_CMSDK_BASE_S: u32 = 0x5802E000;
    pub const SLOWCLK_TIMER_CMSDK_BASE_S: u32 = 0x5802F000;
    pub const SYSWDOG_ARMV8_M_CNTRL_BASE_S: u32 = 0x58040000;
    pub const SYSWDOG_ARMV8_M_REFRESH_BASE_S: u32 = 0x58041000;
    pub const SYSCNTR_CNTRL_BASE_S: u32 = 0x58100000;
    pub const SYSCNTR_READ_BASE_S: u32 = 0x58101000;

    // Secure MSTEXPPIHL Peripheral region
    pub const UART0_BASE_S: u32 = 0x59303000;
    pub const UART1_BASE_S: u32 = 0x59304000;
    pub const UART2_BASE_S: u32 = 0x59305000;
    pub const UART3_BASE_S: u32 = 0x59306000;
    pub const UART4_BASE_S: u32 = 0x59307000;
}

pub const SYSTEM_CORE_CLOCK: u32 = 25000000;

pub const UART0_CLOCK: u32 = 25000000;
pub const UART0_NAME: &CStr = c"uart0";
pub const UART1_CLOCK: u32 = 25000000;
pub const UART1_NAME: &CStr = c"uart1";
pub const CONSOLE_DEVICE_NAME: *const core::ffi::c_char = UART0_NAME.as_ptr();

pub fn get_system_core_clock() -> u64 {
    SYSTEM_CORE_CLOCK as u64
}
