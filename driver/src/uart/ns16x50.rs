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

use blueos_hal::{
    err::{HalError, Result},
    isr::IsrDesc,
    uart::Uart,
    Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, PlatPeri,
};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

use crate::static_ref::StaticRef;

#[cfg(not(target_board = "rk3568"))]
// qemu virt platform uses NS16550 UART
// NS16550 uses 8-bit registers, and the register offset is 1 byte.
register_structs! {
    UartRegisters {
        /// Get or Put Register.
        (0x00 => rbr: ReadWrite<u8>),
        (0x01 => ier: ReadWrite<u8, IER::Register>),
        (0x02 => fcr: ReadWrite<u8>),
        (0x03 => lcr: ReadWrite<u8>),
        (0x04 => mcr: ReadWrite<u8>),
        (0x05 => lsr: ReadOnly<u8, LSR::Register>),
        (0x06 => msr: ReadOnly<u8>),
        (0x07 => @END),
    }
}

#[cfg(target_board = "rk3568")]
// rk3568 uses NS16650 UART
// NS16650 uses 32-bit registers, and the register offset is 4 bytes.
register_structs! {
    UartRegisters {
        /// Get or Put Register.
        (0x00 => rbr: ReadWrite<u32>),
        (0x04 => ier: ReadWrite<u32, IER::Register>),
        (0x08 => fcr: ReadWrite<u32>),
        (0x0c => lcr: ReadWrite<u32>),
        (0x10 => mcr: ReadWrite<u32>),
        (0x14 => lsr: ReadOnly<u32, LSR::Register>),
        (0x18 => msr: ReadOnly<u32>),
        (0x1c => scr: ReadWrite<u32>),
        (0x20 => lpdll: ReadWrite<u32>),
        (0x24 => _reserved0),
        /// Uart Status Register.
        (0x7c => usr: ReadOnly<u32>),
        (0x80 => _reserved1),
        (0x88 => srr: ReadWrite<u32>),
        (0x8c => _reserved2),
        (0xc0 => dlf: ReadWrite<u32>),
        (0xc4 => @END),
    }
}

macro_rules! define_ns16x50_registers {
    ($base:ident) => {
        register_bitfields! [$base,
            LSR [
                DATA_READY OFFSET(0) NUMBITS(1) [],
                OVERRUN_ERROR OFFSET(1) NUMBITS(1) [],
                PARITY_ERROR OFFSET(2) NUMBITS(1) [],
                FRAMING_ERROR OFFSET(3) NUMBITS(1) [],
                BREAK_INTERRUPT OFFSET(4) NUMBITS(1) [],
                TRANS_HOLD_REG_EMPTY OFFSET(5) NUMBITS(1) [],
                TRANS_EMPTY OFFSET(6) NUMBITS(1) [],
                RECV_FIFO_ERROR OFFSET(7) NUMBITS(1) [],
            ],

            IER [
                RECV_DATA_AVAILABLE OFFSET(0) NUMBITS(1) [],
                TRANS_HOLD_EMPTY OFFSET(1) NUMBITS(1) [],
                RECV_LINE_STATUS OFFSET(2) NUMBITS(1) [],
                MODEM_STATUS OFFSET(3) NUMBITS(1) [],
                PROG_THRE OFFSET(5) NUMBITS(1) [],
            ],

            LCR [
                WORD_LENGTH OFFSET(0) NUMBITS(2) [],
                STOP_BITS OFFSET(2) NUMBITS(1) [],
                PARITY_ENABLE OFFSET(3) NUMBITS(1) [],
                EVEN_PARITY OFFSET(4) NUMBITS(1) [],
                STICK_PARITY OFFSET(5) NUMBITS(1) [],
                BREAK_CONTROL OFFSET(6) NUMBITS(1) [],
                DLAB OFFSET(7) NUMBITS(1) [],
            ],

            FCR [
                ENABLE OFFSET(0) NUMBITS(1) [],
                CLEAR_RX OFFSET(1) NUMBITS(1) [],
                CLEAR_TX OFFSET(2) NUMBITS(1) [],
                TRIGGER_LEVEL OFFSET(6) NUMBITS(2) [],
            ],

            IIR [
                NO_INTERRUPT_PENDING OFFSET(0) NUMBITS(1) [],
                INTERRUPT_ID OFFSET(1) NUMBITS(3) [],
            ],
        ];
    }
}

const IIR_ID_MODEM_STATUS: u32 = 0b000;
const IIR_ID_TX_EMPTY: u32 = 0b001;
const IIR_ID_RX_AVAILABLE: u32 = 0b010;
const IIR_ID_RX_LINE_STATUS: u32 = 0b011;
const IIR_ID_RX_TIMEOUT: u32 = 0b110;
const MAX_PENDING_INTERRUPTS_TO_CLEAR: usize = 16;

#[cfg(not(target_board = "rk3568"))]
define_ns16x50_registers!(u8);

#[cfg(target_board = "rk3568")]
define_ns16x50_registers!(u32);

pub struct Ns16x50 {
    registers: StaticRef<UartRegisters>,
}

impl Ns16x50 {
    pub const fn new(base: usize) -> Self {
        Self {
            registers: unsafe { StaticRef::new(base as *const UartRegisters) },
        }
    }

    #[cfg(not(target_board = "rk3568"))]
    fn set_fcr(&self, value: u32) {
        self.registers.fcr.set(value as u8);
    }

    #[cfg(target_board = "rk3568")]
    fn set_fcr(&self, value: u32) {
        self.registers.fcr.set(value);
    }

    #[cfg(not(target_board = "rk3568"))]
    fn iir(&self) -> u32 {
        self.registers.fcr.get() as u32
    }

    #[cfg(target_board = "rk3568")]
    fn iir(&self) -> u32 {
        self.registers.fcr.get()
    }

    #[cfg(not(target_board = "rk3568"))]
    fn lcr(&self) -> u32 {
        self.registers.lcr.get() as u32
    }

    #[cfg(target_board = "rk3568")]
    fn lcr(&self) -> u32 {
        self.registers.lcr.get()
    }

    #[cfg(not(target_board = "rk3568"))]
    fn set_lcr(&self, value: u32) {
        self.registers.lcr.set(value as u8);
    }

    #[cfg(target_board = "rk3568")]
    fn set_lcr(&self, value: u32) {
        self.registers.lcr.set(value);
    }

    #[cfg(not(target_board = "rk3568"))]
    fn set_mcr(&self, value: u32) {
        self.registers.mcr.set(value as u8);
    }

    #[cfg(target_board = "rk3568")]
    fn set_mcr(&self, value: u32) {
        self.registers.mcr.set(value);
    }

    fn set_interrupt_enable(&self, intr: super::InterruptType, enable: bool) {
        match intr {
            super::InterruptType::Rx => {
                if enable {
                    self.registers
                        .ier
                        .modify(IER::RECV_DATA_AVAILABLE::SET + IER::RECV_LINE_STATUS::SET);
                } else {
                    self.registers
                        .ier
                        .modify(IER::RECV_DATA_AVAILABLE::CLEAR + IER::RECV_LINE_STATUS::CLEAR);
                }
            }
            super::InterruptType::Tx => {
                if enable {
                    self.registers.ier.modify(IER::TRANS_HOLD_EMPTY::SET);
                } else {
                    self.registers.ier.modify(IER::TRANS_HOLD_EMPTY::CLEAR);
                }
            }
            super::InterruptType::All => {
                self.set_interrupt_enable(super::InterruptType::Rx, enable);
                self.set_interrupt_enable(super::InterruptType::Tx, enable);
            }
            _ => {}
        }
    }

    fn clear_pending_interrupt(&self, iir: u32) -> bool {
        match (iir >> 1) & 0b111 {
            IIR_ID_RX_LINE_STATUS => {
                let _ = self.registers.lsr.get();
                true
            }
            IIR_ID_RX_AVAILABLE | IIR_ID_RX_TIMEOUT => {
                while !self.is_rx_fifo_empty() {
                    let _ = self.registers.rbr.get();
                }
                true
            }
            IIR_ID_TX_EMPTY => false,
            IIR_ID_MODEM_STATUS => {
                let _ = self.registers.msr.get();
                true
            }
            _ => true,
        }
    }
}

impl Configuration<super::UartConfig> for Ns16x50 {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<()> {
        let word_length = match param.data_bits {
            super::DataBits::DataBits5 => 0b00,
            super::DataBits::DataBits6 => 0b01,
            super::DataBits::DataBits7 => 0b10,
            super::DataBits::DataBits8 => 0b11,
            super::DataBits::DataBits9 => return Err(HalError::InvalidParam),
        };

        let stop_bits = match param.stop_bits {
            super::StopBits::DataBits1 => 0,
            super::StopBits::DataBits2 => 1,
            super::StopBits::DataBits1_5 if param.data_bits == super::DataBits::DataBits5 => 1,
            super::StopBits::DataBits0_5 | super::StopBits::DataBits1_5 => {
                return Err(HalError::InvalidParam);
            }
        };

        let parity = match param.parity {
            super::Parity::None => 0,
            super::Parity::Odd => 1 << 3,
            super::Parity::Even => (1 << 3) | (1 << 4),
            super::Parity::Mark => (1 << 3) | (1 << 5),
            super::Parity::Space => (1 << 3) | (1 << 4) | (1 << 5),
        };

        if param.flow_ctrl != super::FlowCtrl::None {
            return Err(HalError::NotSupport);
        }

        self.set_lcr(word_length | (stop_bits << 2) | parity);
        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Ns16x50 {
    fn set_break_signal(&self, enable: bool) -> Result<()> {
        let mut lcr = self.lcr();
        if enable {
            lcr |= 1 << 6;
        } else {
            lcr &= !(1 << 6);
        }
        self.set_lcr(lcr);
        Ok(())
    }
}

impl Has8bitDataReg for Ns16x50 {
    fn read_data8(&self) -> Result<u8> {
        if !self.is_data_ready() {
            return Err(HalError::NotReady);
        }

        let er_bits = self.registers.lsr.get();
        if LSR::FRAMING_ERROR.is_set(er_bits)
            || LSR::OVERRUN_ERROR.is_set(er_bits)
            || LSR::PARITY_ERROR.is_set(er_bits)
            || LSR::RECV_FIFO_ERROR.is_set(er_bits)
        {
            Err(blueos_hal::err::HalError::IoError)
        } else {
            Ok(self.registers.rbr.get() as u8)
        }
    }

    fn write_data8(&self, data: u8) {
        #[cfg(not(target_board = "rk3568"))]
        self.registers.rbr.set(data as u8);
        #[cfg(target_board = "rk3568")]
        self.registers.rbr.set(data as u32);
    }

    fn is_data_ready(&self) -> bool {
        self.registers.lsr.is_set(LSR::DATA_READY)
    }
}

impl HasLineStatusReg for Ns16x50 {
    fn is_bus_busy(&self) -> bool {
        !self.registers.lsr.is_set(LSR::TRANS_EMPTY)
    }
}

impl HasFifo for Ns16x50 {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        let trigger_level = match num {
            1 => 0,
            4 => 1,
            8 => 2,
            14 => 3,
            _ => return Err(HalError::InvalidParam),
        };

        self.set_fcr(1 | (1 << 1) | (1 << 2) | (trigger_level << 6));
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        !self.registers.lsr.is_set(LSR::TRANS_HOLD_REG_EMPTY)
    }

    fn is_rx_fifo_empty(&self) -> bool {
        !self.registers.lsr.is_set(LSR::DATA_READY)
    }
}

impl HasInterruptReg for Ns16x50 {
    type InterruptType = super::InterruptType;

    fn clear_interrupt(&self, int_type: Self::InterruptType) {
        match int_type {
            super::InterruptType::Rx => {
                let iir = self.iir();
                match (iir >> 1) & 0b111 {
                    IIR_ID_RX_AVAILABLE | IIR_ID_RX_LINE_STATUS | IIR_ID_RX_TIMEOUT
                        if iir & 1 == 0 =>
                    {
                        self.clear_pending_interrupt(iir);
                    }
                    _ => {
                        let _ = self.registers.lsr.get();
                    }
                }
            }
            super::InterruptType::Tx => {
                let iir = self.iir();
                if iir & 1 == 0 && (iir >> 1) & 0b111 == IIR_ID_TX_EMPTY {
                    let _ = iir;
                }
            }
            super::InterruptType::All => {
                for _ in 0..MAX_PENDING_INTERRUPTS_TO_CLEAR {
                    let iir = self.iir();
                    if iir & 1 != 0 {
                        break;
                    }
                    if !self.clear_pending_interrupt(iir) {
                        break;
                    }
                }
                if self.registers.lsr.is_set(LSR::DATA_READY)
                    || self.registers.lsr.is_set(LSR::RECV_FIFO_ERROR)
                {
                    let _ = self.registers.lsr.get();
                }
            }
            _ => {}
        }
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        self.set_interrupt_enable(intr, false);
    }

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        self.set_interrupt_enable(intr, true);
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        let iir = self.iir();
        if iir & 1 != 0 {
            return super::InterruptType::Unknown;
        }

        match (iir >> 1) & 0b111 {
            IIR_ID_TX_EMPTY => super::InterruptType::Tx,
            IIR_ID_RX_AVAILABLE | IIR_ID_RX_LINE_STATUS | IIR_ID_RX_TIMEOUT => {
                super::InterruptType::Rx
            }
            IIR_ID_MODEM_STATUS => super::InterruptType::Unknown,
            _ => super::InterruptType::Unknown,
        }
    }
}

unsafe impl Sync for Ns16x50 {}
unsafe impl Send for Ns16x50 {}

impl PlatPeri for Ns16x50 {
    fn enable(&self) {
        self.set_mcr((1 << 0) | (1 << 1) | (1 << 3));
    }

    fn disable(&self) {
        self.disable_interrupt(super::InterruptType::All);
        self.set_mcr(0);
    }
}

pub struct Ns16x50Isr<const DEVICE_ADDRESS: usize, T: Sync + 'static> {
    pub data: &'static T,
    pub tx_isr: Option<fn(&T)>,
    pub rx_isr: Option<fn(&T)>,
}

impl<const DEVICE_ADDRESS: usize, T: Sync + 'static> Ns16x50Isr<DEVICE_ADDRESS, T> {
    pub const fn new(data: &'static T, tx_isr: Option<fn(&T)>, rx_isr: Option<fn(&T)>) -> Self {
        Self {
            data,
            tx_isr,
            rx_isr,
        }
    }
}

impl<const DEVICE_ADDRESS: usize, T: Sync> IsrDesc for Ns16x50Isr<DEVICE_ADDRESS, T> {
    fn service_isr(&self) {
        let register: StaticRef<UartRegisters> =
            unsafe { StaticRef::new(DEVICE_ADDRESS as *const UartRegisters) };

        for _ in 0..MAX_PENDING_INTERRUPTS_TO_CLEAR {
            let iir = register.fcr.get() as u32;
            if iir & 1 != 0 {
                break;
            }

            match (iir >> 1) & 0b111 {
                IIR_ID_RX_LINE_STATUS => {
                    let _ = register.lsr.get();
                    if let Some(rx_isr) = self.rx_isr {
                        rx_isr(self.data);
                    }
                }
                IIR_ID_RX_AVAILABLE | IIR_ID_RX_TIMEOUT => {
                    if let Some(rx_isr) = self.rx_isr {
                        rx_isr(self.data);
                    }
                }
                IIR_ID_TX_EMPTY => {
                    if let Some(tx_isr) = self.tx_isr {
                        tx_isr(self.data);
                    }
                }
                IIR_ID_MODEM_STATUS => {
                    let _ = register.msr.get();
                }
                _ => break,
            }
        }
    }
}
