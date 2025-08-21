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
            termios::{Cflags, Termios},
        },
        DeviceRequest,
    },
};
use bitflags::bitflags;
use core::{fmt, ptr::NonNull};
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use safe_mmio::{
    field, field_shared,
    fields::{ReadPure, ReadPureWrite, ReadWrite, WriteOnly},
    UniqueMmioPointer,
};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

// Register descriptions
// see: https://developer.arm.com/documentation/ddi0183/g/programmers-model/register-descriptions

/// Data Register
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct DataRegister(u32);

/// Receive Status Register/SerialError Clear Register, UARTRSR/UARTECR
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct ReceiveStatusRegister(u32);

/// Flag Register, UARTFR
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct FlagsRegister(u32);

/// Line Control Register, UARTLCR_H
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct LineControlRegister(u32);

/// Control Register, UARTCR
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct ControlRegister(u32);

/// Set of interrupts. This is used for the interrupt status registers (UARTRIS and UARTMIS),
/// interrupt mask register (UARTIMSC) and and interrupt clear register (UARTICR).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct Interrupts(u32);

bitflags! {
    impl DataRegister: u32 {
        /// Overrun error
        const OE = 1 << 11;
        /// Break error
        const BE = 1 << 10;
        /// Parity error
        const PE = 1 << 9;
        /// Framing error
        const FE = 1 << 8;
    }

    impl ReceiveStatusRegister: u32 {
        /// Overrun error
        const OE = 1 << 3;
        /// Break error
        const BE = 1 << 2;
        /// Parity error
        const PE = 1 << 1;
        /// Framing error
        const FE = 1 << 0;
    }

    impl FlagsRegister: u32 {
        /// Ring indicator
        const RI = 1 << 8;
        /// Transmit FIFO is empty
        const TXFE = 1 << 7;
        /// Receive FIFO is full
        const RXFF = 1 << 6;
        /// Transmit FIFO is full
        const TXFF = 1 << 5;
        /// Receive FIFO is empty
        const RXFE = 1 << 4;
        /// UART busy
        const BUSY = 1 << 3;
        /// Data carrier detect
        const DCD = 1 << 2;
        /// Data set ready
        const DSR = 1 << 1;
        /// Clear to send
        const CTS = 1 << 0;
    }

    impl LineControlRegister: u32 {
        /// Stick parity select.
        const SPS = 1 << 7;
        /// Word length
        const WLEN_5BITS = 0b00 << 5;
        const WLEN_6BITS = 0b01 << 5;
        const WLEN_7BITS = 0b10 << 5;
        const WLEN_8BITS = 0b11 << 5;
        /// Enable FIFOs
        const FEN = 1 << 4;
        /// Two stop bits select
        const STP2 = 1 << 3;
        /// Even parity select
        const EPS = 1 << 2;
        /// Parity enable
        const PEN = 1 << 1;
        /// Send break
        const BRK = 1 << 0;
    }

    impl ControlRegister: u32 {
        /// CTS hardware flow control enable
        const CTSEn = 1 << 15;
        /// RTS hardware flow control enable
        const RTSEn = 1 << 14;
        /// This bit is the complement of the UART Out2 (nUARTOut2) modem status output
        const Out2 = 1 << 13;
        /// This bit is the complement of the UART Out1 (nUARTOut1) modem status output
        const Out1 = 1 << 12;
        /// Request to send
        const RTS = 1 << 11;
        /// Data transmit ready
        const DTR = 1 << 10;
        /// Receive enable
        const RXE = 1 << 9;
        /// Transmit enable
        const TXE = 1 << 8;
        /// Loopback enable
        const LBE = 1 << 7;
        /// SIR low-power IrDA mode
        const SIRLP = 1 << 2;
        /// SIR enable
        const SIREN = 1 << 1;
        /// UART enable
        const UARTEN = 1 << 0;
    }

    impl Interrupts: u32 {
        /// Overrun error interrupt.
        const OEI = 1 << 10;
        /// Break error interrupt.
        const BEI = 1 << 9;
        /// Parity error interrupt.
        const PEI = 1 << 8;
        /// Framing error interrupt.
        const FEI = 1 << 7;
        /// Receive timeout interrupt.
        const RTI = 1 << 6;
        /// Transmit interrupt.
        const TXI = 1 << 5;
        /// Receive interrupt.
        const RXI = 1 << 4;
        /// nUARTDSR modem interrupt.
        const DSRMI = 1 << 3;
        /// nUARTDCD modem interrupt.
        const DCDMI = 1 << 2;
        /// nUARTCTS modem interrupt.
        const CTSMI = 1 << 1;
        /// nUARTRI modem interrupt.
        const RIMI = 1 << 0;
    }
}

/// Set all interrupts from bit 0 to 10
pub const ALL_INTERRUPTS: Interrupts = Interrupts::from_bits_truncate(0x7FF);

/// PL011 register map
#[derive(Clone, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
#[repr(C, align(4))]
pub struct PL011Registers {
    /// 0x000: Data Register
    uartdr: ReadWrite<u32>,
    /// 0x004: Receive Status Register/SerialError Clear Register
    uartrsr_ecr: ReadPureWrite<u32>,
    /// 0x008 - 0x014
    reserved_08: [u32; 4],
    /// 0x018: Flag Register
    uartfr: ReadPure<FlagsRegister>,
    /// 0x01C
    reserved_1c: u32,
    /// 0x020: IrDA Low-Power Counter Register
    uartilpr: ReadPureWrite<u32>,
    /// 0x024: Integer Baud Rate Register
    uartibrd: ReadPureWrite<u32>,
    /// 0x028: Fractional Baud Rate Register
    uartfbrd: ReadPureWrite<u32>,
    /// 0x02C: Line Control Register
    uartlcr_h: ReadPureWrite<LineControlRegister>,
    /// 0x030: Control Register
    uartcr: ReadPureWrite<ControlRegister>,
    /// 0x034: Interrupt FIFO Level Select Register
    uartifls: ReadPureWrite<u32>,
    /// 0x038: Interrupt Mask Set/Clear Register
    uartimsc: ReadPureWrite<Interrupts>,
    /// 0x03C: Raw Interrupt Status Register
    uartris: ReadPure<Interrupts>,
    /// 0x040: Masked INterrupt Status Register
    uartmis: ReadPure<Interrupts>,
    /// 0x044: Interrupt Clear Register
    uarticr: WriteOnly<Interrupts>,
    /// 0x048: DMA control Register
    uartdmacr: ReadPureWrite<u32>,
    /// 0x04C - 0xFDC
    reserved_4c: [u32; 997],
    /// 0xFE0: UARTPeriphID0 Register
    uartperiphid0: ReadPure<u32>,
    /// 0xFE4: UARTPeriphID1 Register
    uartperiphid1: ReadPure<u32>,
    /// 0xFE8: UARTPeriphID2 Register
    uartperiphid2: ReadPure<u32>,
    /// 0xFEC: UARTPeriphID3 Register
    uartperiphid3: ReadPure<u32>,
    /// 0xFF0: UARTPCellID0 Register
    uartpcellid0: ReadPure<u32>,
    /// 0xFF4: UARTPCellID1 Register
    uartpcellid1: ReadPure<u32>,
    /// 0xFF8: UARTPCellID2 Register
    uartpcellid2: ReadPure<u32>,
    /// 0xFFC: UARTPCellID3 Register
    uartpcellid3: ReadPure<u32>,
}

/// RX/TX interrupt FIFO levels
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FifoLevel {
    Bytes4 = 0b000,
    Bytes8 = 0b001,
    Bytes16 = 0b010,
    Bytes24 = 0b011,
    Bytes28 = 0b100,
}

/// UART peripheral identification structure
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Identification {
    pub part_number: u16,
    pub designer: u8,
    pub revision_number: u8,
    pub configuration: u8,
}

impl Identification {
    const PART_NUMBER: u16 = 0x11;
    const DESIGNER_ARM: u8 = b'A';
    const REVISION_MAX: u8 = 0x03;
    const CONFIGURATION: u8 = 0x00;

    /// Check if the identification block describes a valid PL011 peripheral
    pub fn is_valid(&self) -> bool {
        self.part_number == Self::PART_NUMBER
            && self.designer == Self::DESIGNER_ARM
            && self.revision_number <= Self::REVISION_MAX
            && self.configuration == Self::CONFIGURATION
    }
}

/// PL011 UART implementation
pub struct Uart<'a> {
    regs: UniqueMmioPointer<'a, PL011Registers>,
}

impl<'a> Uart<'a> {
    /// Creates new UART instance.
    pub fn new(regs: UniqueMmioPointer<'a, PL011Registers>) -> Self {
        Self { regs }
    }

    /// Configure and enable UART
    pub fn enable(&mut self, termios: &Termios, sysclk: u32) -> Result<(), SerialError> {
        // Baud rate
        let (uartibrd, uartfbrd) = Self::calculate_baud_rate_divisor(termios.getospeed(), sysclk)?;

        // Line control register
        let line_control = if termios.cflag.contains(Cflags::CSIZE_8) {
            LineControlRegister::WLEN_8BITS
        } else if termios.cflag.contains(Cflags::CSIZE_7) {
            LineControlRegister::WLEN_7BITS
        } else if termios.cflag.contains(Cflags::CSIZE_6) {
            LineControlRegister::WLEN_6BITS
        } else {
            LineControlRegister::WLEN_5BITS
        } | if !termios.cflag.contains(Cflags::PARENB) {
            LineControlRegister::empty()
        } else if termios.cflag.contains(Cflags::PARODD) {
            LineControlRegister::PEN
        } else {
            LineControlRegister::PEN | LineControlRegister::EPS
        } | if termios.cflag.contains(Cflags::CSTOPB) {
            LineControlRegister::STP2
        } else {
            LineControlRegister::empty()
        };

        field!(self.regs, uartrsr_ecr).write(0);
        field!(self.regs, uartcr).write(ControlRegister::empty());

        field!(self.regs, uartibrd).write(uartibrd);
        field!(self.regs, uartfbrd).write(uartfbrd);
        field!(self.regs, uartlcr_h).write(line_control);

        field!(self.regs, uartcr)
            .write(ControlRegister::RXE | ControlRegister::TXE | ControlRegister::UARTEN);

        Ok(()) // Refactor: no SerialError returned so far, could be independent from SerialError?
    }

    /// Disable UART
    pub fn disable(&mut self) {
        field!(self.regs, uartcr).write(ControlRegister::empty());
    }

    /// Check if receive FIFO is empty
    pub fn is_rx_fifo_empty(&self) -> bool {
        self.flags().contains(FlagsRegister::RXFE)
    }

    /// Check if receive FIFO is full
    pub fn is_rx_fifo_full(&self) -> bool {
        self.flags().contains(FlagsRegister::RXFF)
    }

    /// Check if transmit FIFO is empty
    pub fn is_tx_fifo_empty(&self) -> bool {
        self.flags().contains(FlagsRegister::TXFE)
    }

    /// Check if transmit FIFO is full
    pub fn is_tx_fifo_full(&self) -> bool {
        self.flags().contains(FlagsRegister::TXFF)
    }

    /// Check if UART is busy
    pub fn is_busy(&self) -> bool {
        self.flags().contains(FlagsRegister::BUSY)
    }

    /// Reads and returns the flag register.
    fn flags(&self) -> FlagsRegister {
        field_shared!(self.regs, uartfr).read()
    }

    /// Non-blocking read of a single byte from the UART.
    ///
    /// Returns `Ok(None)` if no data is available to read.
    pub fn read_word(&mut self) -> Result<Option<u8>, SerialError> {
        if self.is_rx_fifo_empty() {
            return Ok(None);
        }

        let dr = field!(self.regs, uartdr).read();

        let flags = DataRegister::from_bits_truncate(dr);

        if flags.contains(DataRegister::OE) {
            return Err(SerialError::Overrun);
        } else if flags.contains(DataRegister::BE) {
            return Err(SerialError::Break);
        } else if flags.contains(DataRegister::PE) {
            return Err(SerialError::Parity);
        } else if flags.contains(DataRegister::FE) {
            return Err(SerialError::Framing);
        }

        Ok(Some(dr as u8))
    }

    /// Non-blocking write of a single byte to the UART
    pub fn write_word(&mut self, word: u8) {
        field!(self.regs, uartdr).write(word as u32);
    }

    pub fn try_write_data(&mut self, byte: u8) -> Result<(), SerialError> {
        if self.is_tx_fifo_full() {
            Err(SerialError::Overrun)
        } else {
            self.write_word(byte);
            Ok(())
        }
    }

    /// Read UART peripheral identification structure
    pub fn read_identification(&self) -> Identification {
        // SAFETY: The caller of UniqueMmioPointer::new promised that it wraps a valid and unique
        // register block.
        let id: [u32; 4] = {
            [
                field_shared!(self.regs, uartperiphid0).read(),
                field_shared!(self.regs, uartperiphid1).read(),
                field_shared!(self.regs, uartperiphid2).read(),
                field_shared!(self.regs, uartperiphid3).read(),
            ]
        };

        Identification {
            part_number: (id[0] & 0xff) as u16 | ((id[1] & 0x0f) << 8) as u16,
            designer: ((id[1] & 0xf0) >> 4) as u8 | ((id[2] & 0x0f) << 4) as u8,
            revision_number: ((id[2] & 0xf0) >> 4) as u8,
            configuration: (id[3] & 0xff) as u8,
        }
    }

    fn calculate_baud_rate_divisor(baud_rate: u32, sysclk: u32) -> Result<(u32, u32), SerialError> {
        // baud_div = sysclk / (baud_rate * 16)
        // baud_div_bits = (baud_div * 2^7 + 1) / 2
        // After simplifying:
        // baud_div_bits = ((sysclk * 8 / baud_rate) + 1) / 2
        let baud_div = sysclk
            .checked_mul(8)
            .and_then(|clk| clk.checked_div(baud_rate))
            .ok_or(SerialError::InvalidParameter)?;
        let baud_div_bits = baud_div
            .checked_add(1)
            .map(|div| div >> 1)
            .ok_or(SerialError::InvalidParameter)?;

        let ibrd = baud_div_bits >> 6;
        let fbrd = baud_div_bits & 0x3F;

        if ibrd == 0 || (ibrd == 0xffff && fbrd != 0) || ibrd > 0xffff {
            return Err(SerialError::InvalidParameter);
        }

        Ok((ibrd, fbrd))
    }

    /// Sets trigger levels for RX and TX interrupts.
    /// The interrupts are generated when the fill level progresses through the trigger level.
    pub fn set_interrupt_fifo_levels(&mut self, rx_level: FifoLevel, tx_level: FifoLevel) {
        let fifo_levels = ((rx_level as u32) << 3) | tx_level as u32;

        field!(self.regs, uartifls).write(fifo_levels);
    }

    /// Reads the raw interrupt status register.
    pub fn raw_interrupt_status(&self) -> Interrupts {
        field_shared!(self.regs, uartris).read()
    }

    /// Reads the masked interrupt status register.
    pub fn masked_interrupt_status(&self) -> Interrupts {
        field_shared!(self.regs, uartmis).read()
    }

    /// Returns the current set of interrupt masks.
    pub fn interrupt_masks(&self) -> Interrupts {
        field_shared!(self.regs, uartimsc).read()
    }

    /// Sets the interrupt masks.
    pub fn set_interrupt_masks(&mut self, masks: Interrupts) {
        field!(self.regs, uartimsc).write(masks)
    }

    /// Clears the given set of interrupts.
    pub fn clear_interrupts(&mut self, interrupts: Interrupts) {
        field!(self.regs, uarticr).write(interrupts)
    }
}

// SAFETY: An `&Uart` only allows operations which read registers, which can safely be done from
// multiple threads simultaneously.
unsafe impl Sync for Uart<'_> {}

impl fmt::Write for Uart<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for byte in s.as_bytes() {
            // Wait until there is room in the TX buffer.
            while self.is_tx_fifo_full() {}
            self.write_word(*byte);
        }
        Ok(())
    }
}

impl Drop for Uart<'_> {
    fn drop(&mut self) {
        self.disable();
    }
}

pub struct Driver<'a> {
    uart: Uart<'a>,
    clock: u32,
    irq: irq::IrqNumber,
}

impl Driver<'_> {
    pub fn new(base_address: u64, clock: u32, irq: irq::IrqNumber) -> Self {
        Self {
            uart: Uart::new(unsafe {
                UniqueMmioPointer::new(NonNull::new(base_address as *mut _).unwrap())
            }),
            clock,
            irq,
        }
    }

    pub fn enable(&mut self, termios: &Termios) {
        self.uart.enable(termios, self.clock);
    }
}

impl ErrorType for Driver<'_> {
    type Error = SerialError;
}

impl Write for Driver<'_> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
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

    fn flush(&mut self) -> Result<(), Self::Error> {
        while self.uart.is_busy() {}
        Ok(())
    }
}

impl WriteReady for Driver<'_> {
    fn write_ready(&mut self) -> Result<bool, SerialError> {
        Ok(!self.uart.is_tx_fifo_full())
    }
}

impl Read for Driver<'_> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, SerialError> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut count = 0;
        while count < buf.len() {
            match self.uart.read_word() {
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

impl ReadReady for Driver<'_> {
    fn read_ready(&mut self) -> Result<bool, SerialError> {
        Ok(!self.uart.is_rx_fifo_empty())
    }
}

impl UartOps for Driver<'_> {
    fn setup(&mut self, termios: &Termios) -> Result<(), SerialError> {
        self.enable(termios);
        self.uart.clear_interrupts(ALL_INTERRUPTS);
        irq::enable_irq_with_priority(self.irq, 0, irq::Priority::Normal);
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), SerialError> {
        self.uart.disable();
        Ok(())
    }

    fn read_byte(&mut self) -> Result<u8, SerialError> {
        match self.uart.read_word()? {
            Some(byte) => Ok(byte),
            None => Err(SerialError::BufferEmpty),
        }
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), SerialError> {
        self.uart.write_word(byte);
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        for c in s.as_bytes() {
            while self.uart.is_tx_fifo_full() {}
            self.uart.write_word(*c);
        }
        Ok(())
    }

    fn set_rx_interrupt(&mut self, enable: bool) {
        let mut masks = self.uart.interrupt_masks();
        if enable {
            masks |= Interrupts::RXI;
        } else {
            masks &= !Interrupts::RXI;
        }
        self.uart.set_interrupt_masks(masks);
    }

    fn set_tx_interrupt(&mut self, enable: bool) {
        let mut masks = self.uart.interrupt_masks();
        if enable {
            masks |= Interrupts::TXI;
        } else {
            masks &= !Interrupts::TXI;
        }
        self.uart.set_interrupt_masks(masks);
    }

    fn clear_rx_interrupt(&mut self) {
        self.uart.clear_interrupts(Interrupts::RXI);
    }

    fn clear_tx_interrupt(&mut self) {
        self.uart.clear_interrupts(Interrupts::TXI);
    }

    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), SerialError> {
        match DeviceRequest::from(request) {
            DeviceRequest::Config => {
                let termios = unsafe { *(arg as *const Termios) };
                self.enable(&termios);
            }
            DeviceRequest::Close => {
                self.uart.disable();
            }
            _ => return Err(SerialError::InvalidParameter),
        }
        Ok(())
    }
}
