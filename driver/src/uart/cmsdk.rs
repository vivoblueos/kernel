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

// SPDX-FileCopyrightText: Copyright 2023-2024 Arm Limited and/or its affiliates <open-source-office@arm.com>
// SPDX-License-Identifier: MIT OR Apache-2.0

use core::cell::UnsafeCell;

use blueos_hal::{
    uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, PlatPeri,
};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

register_bitfields! [
    u32,

    /// Data Register
    pub DATA [
        /// Data value
        DATA OFFSET(0) NUMBITS(8) []
    ],

    /// Status Register
    pub STATE [
        /// Receive overrun
        RXOR OFFSET(3) NUMBITS(1) [],
        /// Transmit overrun
        TXOR OFFSET(2) NUMBITS(1) [],
        /// Receive buffer full
        RXBF OFFSET(1) NUMBITS(1) [],
        /// Transmit buffer full
        TXBF OFFSET(0) NUMBITS(1) []
    ],

    /// Control Register
    pub CTRL [
        /// High-speed test mode
        HSTM OFFSET(6) NUMBITS(1) [],
        /// Receive overrun interrupt enable
        RXORIRQEN OFFSET(5) NUMBITS(1) [],
        /// Transmit overrun interrupt enable
        TXORIRQEN OFFSET(4) NUMBITS(1) [],
        /// Receive interrupt enable
        RXIRQEN OFFSET(3) NUMBITS(1) [],
        /// Transmit interrupt enable
        TXIRQEN OFFSET(2) NUMBITS(1) [],
        /// Receive enable
        RXEN OFFSET(1) NUMBITS(1) [],
        /// Transmit enable
        TXEN OFFSET(0) NUMBITS(1) []
    ],

    /// Interrupt Status Register
    pub INTSTATUS [
        /// Receive overrun interrupt
        RXORIRQ OFFSET(3) NUMBITS(1) [], // write 1 to clear
        /// Transmit overrun interrupt
        TXORIRQ OFFSET(2) NUMBITS(1) [], // write 1 to clear
        /// Receive interrupt
        RXIRQ OFFSET(1) NUMBITS(1) [], // write 1 to clear
        /// Transmit interrupt
        TXIRQ OFFSET(0) NUMBITS(1) [] // write 1 to clear
    ],

    /// Baudrate Divider Register
    pub BAUDDIV [
        /// Baudrate divider
        BAUDDIV OFFSET(0) NUMBITS(20) []
    ]
];

register_structs! {
    /// CMSDK UART Registers
    #[allow(non_snake_case)]
    Registers {
        /// Data Register
        (0x000 => DATA: ReadWrite<u32, DATA::Register>),
        /// Status Register
        (0x004 => STATE: ReadWrite<u32, STATE::Register>),
        /// Control Register
        (0x008 => CTRL: ReadWrite<u32, CTRL::Register>),
        /// Interrupt Status/Clear Register
        (0x00C => INTSTATUS: ReadWrite<u32, INTSTATUS::Register>),
        /// Baudrate Divider Register
        (0x010 => BAUDDIV: ReadWrite<u32, BAUDDIV::Register>),
        (0x014 => @END),
    }
}

/// CMSDK UART peripheral
#[derive(Debug)]
pub struct Cmsdk {
    registers: *mut Registers,
    clk: u32,
    pub intr_handler: UnsafeCell<Option<&'static dyn Fn()>>,
    irq_nums: [u32; 2],
}

impl Cmsdk {
    pub const unsafe fn new(base_addr: *mut u32, clk: u32, tx_irq: u32, rx_irq: u32) -> Self {
        Cmsdk {
            registers: base_addr as *mut Registers,
            clk,
            intr_handler: UnsafeCell::new(None),
            irq_nums: [tx_irq, rx_irq],
        }
    }

    #[inline]
    fn registers(&self) -> &Registers {
        // SAFETY: self.registers points to the control registers of a CMSDK UART device which is
        // appropriately mapped, as promised by the caller of `Uart::new`.
        unsafe { &(*self.registers) }
    }
}

unsafe impl Send for Cmsdk {}
unsafe impl Sync for Cmsdk {}

impl Configuration<super::UartConfig> for Cmsdk {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        let divisor = (self.clk << 2) / param.baudrate;

        self.registers().BAUDDIV.set(divisor);
        self.registers().INTSTATUS.set(0xf);

        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Cmsdk {}

impl Has8bitDataReg for Cmsdk {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        let state = self.registers().STATE.extract();

        if !state.is_set(STATE::RXBF) {
            // no data
            Err(blueos_hal::err::HalError::NotReady)
        } else if state.is_set(STATE::RXOR) {
            Err(blueos_hal::err::HalError::Fail)
        } else {
            let ch = self.registers().DATA.read(DATA::DATA) as u8;
            self.registers().STATE.set(0);
            Ok(ch)
        }
    }

    fn write_data8(&self, data: u8) {
        self.registers().DATA.write(DATA::DATA.val(data as u32));
    }

    fn is_data_ready(&self) -> bool {
        self.registers().STATE.is_set(STATE::RXBF)
    }
}

impl HasLineStatusReg for Cmsdk {
    fn is_bus_busy(&self) -> bool {
        self.registers().STATE.is_set(STATE::TXBF)
    }
}

impl HasFifo for Cmsdk {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        self.registers().STATE.is_set(STATE::TXBF)
    }

    fn is_rx_fifo_empty(&self) -> bool {
        !self.registers().STATE.is_set(STATE::RXBF)
    }
}

impl HasInterruptReg for Cmsdk {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Tx => {
                self.registers().CTRL.modify(CTRL::TXIRQEN::SET);
            }
            super::InterruptType::Rx => {
                self.registers().CTRL.modify(CTRL::RXIRQEN::SET);
            }
            _ => {}
        }
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Tx => {
                self.registers().CTRL.modify(CTRL::TXIRQEN::CLEAR);
            }
            super::InterruptType::Rx => {
                self.registers().CTRL.modify(CTRL::RXIRQEN::CLEAR);
            }
            _ => {}
        }
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Tx => {
                self.registers().INTSTATUS.modify(INTSTATUS::TXIRQ::SET);
            }
            super::InterruptType::Rx => {
                self.registers().INTSTATUS.modify(INTSTATUS::RXIRQ::SET);
            }
            _ => {
                let status = self.registers().INTSTATUS.get();
                self.registers().INTSTATUS.set(status);
            }
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        let state = self.registers().INTSTATUS.extract();

        if state.is_set(INTSTATUS::TXIRQ) {
            super::InterruptType::Tx
        } else if state.is_set(INTSTATUS::RXIRQ) {
            super::InterruptType::Rx
        } else {
            super::InterruptType::Unknown
        }
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {
        unsafe {
            *self.intr_handler.get() = Some(handler);
        }
    }

    fn get_irq_nums(&self) -> &[u32] {
        &self.irq_nums
    }
}

impl PlatPeri for Cmsdk {
    fn enable(&self) {
        self.registers()
            .CTRL
            .modify(CTRL::RXEN::SET + CTRL::TXEN::SET);
    }

    fn disable(&self) {
        self.registers().CTRL.modify(
            CTRL::RXIRQEN::CLEAR + CTRL::RXEN::CLEAR + CTRL::TXIRQEN::CLEAR + CTRL::TXEN::CLEAR,
        );
    }
}
