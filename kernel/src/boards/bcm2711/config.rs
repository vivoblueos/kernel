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

use crate::arch::irq::IrqNumber;
// caculate uart baud rate based on APB clock
pub const APBP_CLOCK: u32 = 0x16e3600;
// https://datasheets.raspberrypi.org/bcm2711/bcm2711-peripherals.pdf
pub const MAIN_PERIPHERAL_BASE: u64 = 0xfe000000;
pub const GPIO_BASE: u64 = 0xfe200000;
pub const PL011_UART0_BASE: u64 = 0xfe201000;
pub const PL011_UART0_IRQNUM: IrqNumber = IrqNumber::new(153);
pub const PSCI_BASE: u32 = 0x84000000;
pub const GICD: usize = 0xFF84_1000;
pub const GICC: usize = 0xFF84_2000;
