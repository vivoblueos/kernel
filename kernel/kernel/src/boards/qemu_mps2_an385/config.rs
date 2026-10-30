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

pub const UART0RX_IRQn: IrqNumber = IrqNumber::new(0);
pub const UART0RX_IRQ_N: u32 = 0;
pub const UART0TX_IRQn: IrqNumber = IrqNumber::new(1);
pub const UART0TX_IRQ_N: u32 = 1;
pub const UART1RX_IRQn: IrqNumber = IrqNumber::new(2);
pub const UART1TX_IRQn: IrqNumber = IrqNumber::new(3);
pub const UART2RX_IRQn: IrqNumber = IrqNumber::new(4);
pub const UART2TX_IRQn: IrqNumber = IrqNumber::new(5);
pub const GPIO0ALL_IRQn: IrqNumber = IrqNumber::new(6);
pub const GPIO1ALL_IRQn: IrqNumber = IrqNumber::new(7);
pub const TIMER0_IRQn: IrqNumber = IrqNumber::new(8);
pub const TIMER1_IRQn: IrqNumber = IrqNumber::new(9);
pub const DUALTIMER_IRQn: IrqNumber = IrqNumber::new(10);
pub const SPI_0_1_IRQn: IrqNumber = IrqNumber::new(11);
pub const UART_0_1_2_OVF_IRQn: IrqNumber = IrqNumber::new(12);
pub const ETHERNET_IRQn: IrqNumber = IrqNumber::new(13);
pub const I2S_IRQn: IrqNumber = IrqNumber::new(14);
pub const TOUCHSCREEN_IRQn: IrqNumber = IrqNumber::new(15);
pub const GPIO2_IRQn: IrqNumber = IrqNumber::new(16);
pub const GPIO3_IRQn: IrqNumber = IrqNumber::new(17);
pub const UART3RX_IRQn: IrqNumber = IrqNumber::new(18);
pub const UART3TX_IRQn: IrqNumber = IrqNumber::new(19);
pub const UART4RX_IRQn: IrqNumber = IrqNumber::new(20);
pub const UART4TX_IRQn: IrqNumber = IrqNumber::new(21);
pub const SPI_2_IRQn: IrqNumber = IrqNumber::new(22);
pub const SPI_3_4_IRQn: IrqNumber = IrqNumber::new(23);
pub const GPIO0_0_IRQn: IrqNumber = IrqNumber::new(24);
pub const GPIO0_1_IRQn: IrqNumber = IrqNumber::new(25);
pub const GPIO0_2_IRQn: IrqNumber = IrqNumber::new(26);
pub const GPIO0_3_IRQn: IrqNumber = IrqNumber::new(27);
pub const GPIO0_4_IRQn: IrqNumber = IrqNumber::new(28);
pub const GPIO0_5_IRQn: IrqNumber = IrqNumber::new(29);
pub const GPIO0_6_IRQn: IrqNumber = IrqNumber::new(30);
pub const GPIO0_7_IRQn: IrqNumber = IrqNumber::new(31);

pub mod memory_map {
    // Peripheral and SRAM base address
    pub const FLASH_BASE: u32 = 0x00000000;
    pub const SRAM_BASE: u32 = 0x20000000;
    pub const PERIPH_BASE: u32 = 0x40000000;
    pub const RAM_BASE: u32 = 0x20000000;
    pub const APB_BASE: u32 = 0x40000000;
    pub const AHB_BASE: u32 = 0x40010000;

    // APB peripherals
    pub const TIMER0_BASE: u32 = APB_BASE;
    pub const TIMER1_BASE: u32 = APB_BASE + 0x1000;
    pub const DUALTIMER_BASE: u32 = APB_BASE + 0x2000;
    pub const DUALTIMER_1_BASE: u32 = DUALTIMER_BASE;
    pub const DUALTIMER_2_BASE: u32 = DUALTIMER_BASE + 0x20;
    pub const UART0_BASE: u32 = APB_BASE + 0x4000;
    pub const UART1_BASE: u32 = APB_BASE + 0x5000;
    pub const UART2_BASE: u32 = APB_BASE + 0x6000;
    pub const WATCHDOG_BASE: u32 = APB_BASE + 0x8000;

    // AHB peripherals
    pub const GPIO0_BASE: u32 = AHB_BASE;
    pub const GPIO1_BASE: u32 = AHB_BASE + 0x1000;
    pub const SYSCTRL_BASE: u32 = AHB_BASE + 0xF000;
}

pub const SYSTEM_CORE_CLOCK: u32 = 25000000;

pub const UART0_NAME: &CStr = c"uart0";
pub const UART1_NAME: &CStr = c"uart1";
pub const CONSOLE_DEVICE_NAME: *const core::ffi::c_char = UART0_NAME.as_ptr();

pub fn get_system_core_clock() -> u64 {
    SYSTEM_CORE_CLOCK as u64
}
