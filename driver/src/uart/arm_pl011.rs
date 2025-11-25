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
use crate::uart::{DataBits, Parity, StopBits};
use bitflags::bitflags;
use blueos_hal::{
    err::{HalError, Result},
    uart::Uart,
    Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, PlatPeri,
};
use core::{cell::UnsafeCell, fmt, ptr::NonNull};
use safe_mmio::{
    field,
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

/// Line Control Register, UARTLCR_H
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct LineControlRegister(u32);

/// Control Register, UARTCR
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct ControlRegister(u32);

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
    pub uartdr: ReadWrite<u32>,
    /// 0x004: Receive Status Register/SerialError Clear Register
    pub uartrsr_ecr: ReadPureWrite<u32>,
    /// 0x008 - 0x014
    reserved_08: [u32; 4],
    /// 0x018: Flag Register
    uartfr: ReadPure<FlagsRegister>,
    /// 0x01C
    reserved_1c: u32,
    /// 0x020: IrDA Low-Power Counter Register
    uartilpr: ReadPureWrite<u32>,
    /// 0x024: Integer Baud Rate Register
    pub uartibrd: ReadPureWrite<u32>,
    /// 0x028: Fractional Baud Rate Register
    pub uartfbrd: ReadPureWrite<u32>,
    /// 0x02C: Line Control Register
    pub uartlcr_h: ReadPureWrite<LineControlRegister>,
    /// 0x030: Control Register
    pub uartcr: ReadPureWrite<ControlRegister>,
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

pub struct ArmPl011<'a> {
    pub regs: UnsafeCell<UniqueMmioPointer<'a, PL011Registers>>,
    pub sysclk: u32,
    pub intr_handler: UnsafeCell<Option<&'static dyn Fn()>>,
    pub reset_ctrl: Option<(&'static dyn blueos_hal::reset::ResetCtrlWithDone, u32)>,
}

impl ArmPl011<'_> {
    pub const fn new(
        base_addr: usize,
        sysclk: u32,
        reset_ctrl: Option<(&'static dyn blueos_hal::reset::ResetCtrlWithDone, u32)>,
    ) -> Self {
        ArmPl011 {
            regs: UnsafeCell::new(unsafe {
                UniqueMmioPointer::new(NonNull::new(base_addr as *mut PL011Registers).unwrap())
            }),
            sysclk,
            intr_handler: UnsafeCell::new(None),
            reset_ctrl,
        }
    }
}

/// Flag Register, UARTFR
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct FlagsRegister(u32);

macro_rules! field_used_by_inner {
    ($mmio_pointer:expr, $field:ident) => {{
        // Make sure $mmio_pointer is the right type.
        let mmio_pointer: &mut UniqueMmioPointer<_> = $mmio_pointer;
        // SAFETY: ptr_mut is guaranteed to return a valid pointer for MMIO, so the pointer to the
        // field must also be valid. MmioPointer::child gives it the same lifetime as the original
        // pointer.
        unsafe {
            let child_pointer =
                core::ptr::NonNull::new(&raw mut (*mmio_pointer.ptr_mut()).$field).unwrap();
            mmio_pointer.child(child_pointer)
        }
    }};
}

impl Configuration<super::UartConfig> for ArmPl011<'static> {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        if let Some(ref reset_ctrl) = self.reset_ctrl {
            let (reset_ctrl, reset_id) = reset_ctrl;
            reset_ctrl.set_reset(*reset_id);
            reset_ctrl.clear_reset(*reset_id);
            reset_ctrl.wait_done(*reset_id);
        }

        // Baud rate
        let (uartibrd, uartfbrd) = calculate_baud_rate_divisor(param.baudrate, self.sysclk)?;

        let line_control = match param.data_bits {
            DataBits::DataBits8 => LineControlRegister::WLEN_8BITS,
            DataBits::DataBits7 => LineControlRegister::WLEN_7BITS,
            DataBits::DataBits6 => LineControlRegister::WLEN_6BITS,
            DataBits::DataBits5 => LineControlRegister::WLEN_5BITS,
            DataBits::DataBits9 => {
                return Err(HalError::InvalidParam);
            }
        };

        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        field_used_by_inner!(unsafe_mut_ref, uartrsr_ecr).write(0);
        field_used_by_inner!(unsafe_mut_ref, uartcr).write(ControlRegister::empty());

        field_used_by_inner!(unsafe_mut_ref, uartibrd).write(uartibrd);
        field_used_by_inner!(unsafe_mut_ref, uartfbrd).write(uartfbrd);
        field_used_by_inner!(unsafe_mut_ref, uartlcr_h).write(line_control);

        field_used_by_inner!(unsafe_mut_ref, uartcr)
            .write(ControlRegister::RXE | ControlRegister::TXE | ControlRegister::UARTEN);

        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus>
    for ArmPl011<'static>
{
}

impl Has8bitDataReg for ArmPl011<'static> {
    fn read_data8(&self) -> Result<u8> {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let data_reg = field_used_by_inner!(unsafe_mut_ref, uartdr).read();

        let flags = DataRegister::from_bits_truncate(data_reg);

        if flags.contains(DataRegister::BE) {
            return Err(HalError::Other("Break Error"));
        } else if flags.contains(DataRegister::PE) {
            return Err(HalError::Other("Parity Error"));
        } else if flags.contains(DataRegister::FE) {
            return Err(HalError::Other("Framing Error"));
        }

        Ok((data_reg & 0xFF) as u8)
    }

    fn write_data8(&self, data: u8) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        field_used_by_inner!(unsafe_mut_ref, uartdr).write(data as u32);
    }

    fn is_data_ready(&self) -> bool {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let flags = field_used_by_inner!(unsafe_mut_ref, uartfr).read();
        !flags.contains(FlagsRegister::RXFE)
    }
}

impl HasLineStatusReg for ArmPl011<'static> {
    fn is_bus_busy(&self) -> bool {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let flags = field_used_by_inner!(unsafe_mut_ref, uartfr).read();
        flags.contains(FlagsRegister::BUSY)
    }
}

impl HasFifo for ArmPl011<'static> {
    fn enable_fifo(&self, num: u8) -> Result<()> {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let ifls_value = match num {
            4 => FifoLevel::Bytes4 as u32,
            8 => FifoLevel::Bytes8 as u32,
            16 => FifoLevel::Bytes16 as u32,
            24 => FifoLevel::Bytes24 as u32,
            28 => FifoLevel::Bytes28 as u32,
            _ => return Err(HalError::InvalidParam),
        };

        // Set RX and TX FIFO levels
        let ifls_reg = (ifls_value << 3) | ifls_value;
        field_used_by_inner!(unsafe_mut_ref, uartifls).write(ifls_reg);

        // Enable FIFOs
        let mut lcr_h = field_used_by_inner!(unsafe_mut_ref, uartlcr_h).read();
        lcr_h |= LineControlRegister::FEN;
        field_used_by_inner!(unsafe_mut_ref, uartlcr_h).write(lcr_h);

        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let flags = field_used_by_inner!(unsafe_mut_ref, uartfr).read();
        flags.contains(FlagsRegister::TXFF)
    }

    fn is_rx_fifo_empty(&self) -> bool {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let flags = field_used_by_inner!(unsafe_mut_ref, uartfr).read();
        flags.contains(FlagsRegister::RXFE)
    }
}

impl HasInterruptReg for ArmPl011<'static> {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let mut imsc = field_used_by_inner!(unsafe_mut_ref, uartimsc).read();
        match intr {
            super::InterruptType::Tx => {
                imsc |= Interrupts::TXI;
            }
            super::InterruptType::Rx => {
                imsc |= Interrupts::RXI;
            }
            _ => {}
        }
        field_used_by_inner!(unsafe_mut_ref, uartimsc).write(imsc);
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let mut imsc = field_used_by_inner!(unsafe_mut_ref, uartimsc).read();
        match intr {
            super::InterruptType::Tx => {
                imsc &= !Interrupts::TXI;
            }
            super::InterruptType::Rx => {
                imsc &= !Interrupts::RXI;
            }
            _ => {}
        }
        imsc &= !Interrupts::from_bits_truncate(intr as u32);
        field_used_by_inner!(unsafe_mut_ref, uartimsc).write(imsc);
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        match intr {
            super::InterruptType::Tx => {
                field_used_by_inner!(unsafe_mut_ref, uarticr).write(Interrupts::TXI);
            }
            super::InterruptType::Rx => {
                field_used_by_inner!(unsafe_mut_ref, uarticr).write(Interrupts::RXI);
            }
            _ => {}
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let mis = field_used_by_inner!(unsafe_mut_ref, uartmis).read();

        if mis.contains(Interrupts::RXI) {
            super::InterruptType::Rx
        } else if mis.contains(Interrupts::TXI) {
            super::InterruptType::Tx
        } else {
            super::InterruptType::Unknown
        }
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {
        let intr_handler_cell = unsafe { &mut *self.intr_handler.get() };
        *intr_handler_cell = Some(handler);
    }

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

unsafe impl Sync for ArmPl011<'static> {}
unsafe impl Send for ArmPl011<'static> {}

impl PlatPeri for ArmPl011<'static> {
    fn enable(&self) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let mut cr = field_used_by_inner!(unsafe_mut_ref, uartcr).read();
        cr |= ControlRegister::UARTEN | ControlRegister::RXE | ControlRegister::TXE;
        field_used_by_inner!(unsafe_mut_ref, uartcr).write(cr);
    }

    fn disable(&self) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        let mut cr = field_used_by_inner!(unsafe_mut_ref, uartcr).read();
        cr &= !(ControlRegister::UARTEN);
        field_used_by_inner!(unsafe_mut_ref, uartcr).write(cr);
    }
}

fn calculate_baud_rate_divisor(baud_rate: u32, sysclk: u32) -> Result<(u32, u32)> {
    // baud_div = sysclk / (baud_rate * 16)
    // baud_div_bits = (baud_div * 2^7 + 1) / 2
    // After simplifying:
    // baud_div_bits = ((sysclk * 8 / baud_rate) + 1) / 2
    let baud_div = sysclk
        .checked_mul(8)
        .and_then(|clk| clk.checked_div(baud_rate))
        .ok_or(HalError::InvalidParam)?;
    let baud_div_bits = baud_div
        .checked_add(1)
        .map(|div| div >> 1)
        .ok_or(HalError::InvalidParam)?;

    let ibrd = baud_div_bits >> 6;
    let fbrd = baud_div_bits & 0x3F;

    if ibrd == 0 || (ibrd == 0xffff && fbrd != 0) || ibrd > 0xffff {
        return Err(HalError::InvalidParam);
    }

    Ok((ibrd, fbrd))
}
