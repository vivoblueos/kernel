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

use crate::{
    arch::irq,
    devices::{
        tty::{
            serial::{SerialError, UartOps},
            termios::Termios,
        },
        DeviceManager, DeviceRequest,
    },
};
use core::hint::spin_loop;
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
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
pub struct Uart {
    registers: *mut Registers,
}

impl Uart {
    /// Constructs a new instance of the UART driver for a CMSDK UART device at the
    /// given base address.
    ///
    /// # Safety
    ///
    /// The given base address must point to the 14 MMIO control registers of a
    /// CMSDK UART device, which must be mapped into the address space of the process
    /// as device memory and not have any other aliases.
    pub const unsafe fn new(base_address: *mut u32) -> Self {
        Self {
            registers: base_address as *mut Registers,
        }
    }

    /// Initializes CMSDK UART.
    ///
    /// clock: Uart clock in Hz.
    /// baud_rate: Baud rate.
    pub fn enable(&mut self, clock: u32, baud_rate: u32) {
        let divisor = (clock << 2) / baud_rate;

        self.registers()
            .CTRL
            .modify(CTRL::RXEN::SET + CTRL::TXEN::SET);
        self.registers().BAUDDIV.set(divisor);
        self.registers().INTSTATUS.set(0xf);
    }

    pub fn disable(&mut self) {
        self.registers().CTRL.modify(
            CTRL::RXIRQEN::CLEAR + CTRL::RXEN::CLEAR + CTRL::TXIRQEN::CLEAR + CTRL::TXEN::CLEAR,
        );
    }

    #[inline]
    pub fn is_transmitting(&self) -> bool {
        self.registers().STATE.is_set(STATE::TXBF)
    }

    #[inline]
    pub fn clear_interrupt(&mut self) {
        let status = self.registers().INTSTATUS.get();
        self.registers().INTSTATUS.set(status);
    }

    #[inline]
    pub fn clear_rx_interrupt(&mut self) {
        self.registers().INTSTATUS.set(INTSTATUS::RXIRQ::SET.into());
    }

    #[inline]
    pub fn clear_tx_interrupt(&mut self) {
        self.registers().INTSTATUS.set(INTSTATUS::TXIRQ::SET.into());
    }

    #[inline]
    pub fn enable_rx_interrupt(&mut self) {
        self.registers().CTRL.modify(CTRL::RXIRQEN::SET);
    }

    #[inline]
    pub fn disable_rx_interrupt(&mut self) {
        self.registers().CTRL.modify(CTRL::RXIRQEN::CLEAR);
    }

    #[inline]
    pub fn enable_tx_interrupt(&mut self) {
        self.registers().CTRL.modify(CTRL::TXIRQEN::SET);
    }

    #[inline]
    pub fn disable_tx_interrupt(&mut self) {
        self.registers().CTRL.modify(CTRL::TXIRQEN::CLEAR);
    }

    /// Reads and returns a pending byte, or `None` if nothing has been
    /// received.
    pub fn read_data(&mut self) -> Result<Option<u8>, SerialError> {
        let state = self.registers().STATE.extract();

        if !state.is_set(STATE::RXBF) {
            // no data
            Ok(None)
        } else if state.is_set(STATE::RXOR) {
            Err(SerialError::Overrun)
        } else {
            let ch = self.registers().DATA.read(DATA::DATA) as u8;
            self.registers().STATE.set(0);
            Ok(Some(ch))
        }
    }

    /// Writes a single byte to the UART.
    pub fn write_data(&mut self, byte: u8) {
        while self.registers().STATE.is_set(STATE::TXBF) {
            spin_loop();
        }

        self.registers().DATA.write(DATA::DATA.val(byte as u32));
    }

    pub fn try_write_data(&mut self, byte: u8) -> Result<(), SerialError> {
        if self.registers().STATE.is_set(STATE::TXBF) {
            Err(SerialError::Overrun)
        } else {
            self.write_data(byte);
            Ok(())
        }
    }

    pub fn is_rx_fifo_full(&self) -> bool {
        self.registers().STATE.is_set(STATE::RXBF)
    }

    pub fn is_tx_fifo_full(&self) -> bool {
        self.registers().STATE.is_set(STATE::TXBF)
    }

    #[inline]
    fn registers(&self) -> &Registers {
        // SAFETY: self.registers points to the control registers of a CMSDK UART device which is
        // appropriately mapped, as promised by the caller of `Uart::new`.
        unsafe { &(*self.registers) }
    }
}

// SAFETY: `Uart` just contains a pointer to device memory, which can be accessed from any context.
// The pointer is guaranteed to be valid and properly aligned by the caller of `Uart::new`.
unsafe impl Send for Uart {}

// SAFETY: Methods on `&Uart` don't allow changing any state so are safe to call concurrently from
// any context. The pointer is guaranteed to be valid and properly aligned by the caller of `Uart::new`.
unsafe impl Sync for Uart {}

impl Drop for Uart {
    fn drop(&mut self) {
        self.disable();
    }
}

impl ErrorType for Driver {
    type Error = SerialError;
}

pub struct Driver {
    uart: Uart,
    clock: u32,
    rx_irq: irq::IrqNumber,
    tx_irq: irq::IrqNumber,
}

impl Driver {
    /// Constructs a new instance of the UART driver for a CMSDK UART device at the
    /// given base address.
    ///
    /// # Safety
    ///
    /// The given base address must point to the 14 MMIO control registers of a
    /// CMSDK UART device, which must be mapped into the address space of the process
    /// as device memory and not have any other aliases.
    pub unsafe fn new(
        base_address: *mut u32,
        clock: u32,
        rx_irq: irq::IrqNumber,
        tx_irq: irq::IrqNumber,
    ) -> Self {
        Self {
            uart: Uart::new(base_address),
            clock,
            rx_irq,
            tx_irq,
        }
    }

    pub fn enable(&mut self, baud_rate: u32) {
        self.uart.enable(self.clock, baud_rate);
    }
}

impl Write for Driver {
    // write will block until all the data is transmitted
    fn write(&mut self, buf: &[u8]) -> Result<usize, SerialError> {
        assert!(!buf.is_empty());
        let mut count = 0;
        // write until the buffer is full
        while count < buf.len() {
            match self.uart.try_write_data(buf[count]) {
                Ok(_) => count += 1,
                Err(_e) => break,
            }
        }
        Ok(count)
    }

    fn flush(&mut self) -> Result<(), SerialError> {
        while self.uart.is_transmitting() {
            spin_loop();
        }
        Ok(())
    }
}

impl WriteReady for Driver {
    fn write_ready(&mut self) -> Result<bool, SerialError> {
        Ok(!self.uart.is_tx_fifo_full())
    }
}

impl Read for Driver {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, SerialError> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut count = 0;
        while count < buf.len() {
            match self.uart.read_data() {
                Ok(Some(byte)) => {
                    buf[count] = byte;
                    count += 1;
                }
                Ok(None) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(count)
    }
}

impl ReadReady for Driver {
    fn read_ready(&mut self) -> Result<bool, SerialError> {
        Ok(self.uart.is_rx_fifo_full())
    }
}

impl UartOps for Driver {
    fn setup(&mut self, termios: &Termios) -> Result<(), SerialError> {
        self.enable(termios.getospeed());
        self.uart.clear_interrupt();
        irq::enable_irq_with_priority(self.rx_irq, irq::Priority::Normal);
        irq::enable_irq_with_priority(self.tx_irq, irq::Priority::Normal);
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), SerialError> {
        irq::disable_irq(self.rx_irq);
        irq::disable_irq(self.tx_irq);
        self.uart.disable();
        Ok(())
    }

    fn read_byte(&mut self) -> Result<u8, SerialError> {
        match self.uart.read_data()? {
            Some(byte) => Ok(byte),
            None => Err(SerialError::BufferEmpty),
        }
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), SerialError> {
        self.uart.write_data(byte);
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        for c in s.as_bytes() {
            self.uart.write_data(*c);
        }
        Ok(())
    }

    fn set_rx_interrupt(&mut self, enable: bool) {
        if enable {
            self.uart.enable_rx_interrupt();
        } else {
            self.uart.disable_rx_interrupt();
        }
    }

    fn set_tx_interrupt(&mut self, enable: bool) {
        if enable {
            self.uart.enable_tx_interrupt();
        } else {
            self.uart.disable_tx_interrupt();
        }
    }

    fn clear_rx_interrupt(&mut self) {
        self.uart.clear_rx_interrupt();
    }

    fn clear_tx_interrupt(&mut self) {
        self.uart.clear_tx_interrupt();
    }

    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), SerialError> {
        match DeviceRequest::from(request) {
            DeviceRequest::Config => {
                let termios = unsafe { *(arg as *const Termios) };
                self.enable(termios.getospeed());
            }
            DeviceRequest::Close => {
                self.uart.disable();
            }
            _ => return Err(SerialError::InvalidParameter),
        }
        Ok(())
    }
}
