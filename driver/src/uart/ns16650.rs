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

use blueos_hal::{
    err::Result, uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg,
    HasLineStatusReg, PlatPeri,
};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

use crate::static_ref::StaticRef;

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

register_bitfields! [u32,
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
    ]
];

pub struct Ns16650 {
    registers: StaticRef<UartRegisters>,
}

impl Ns16650 {
    pub const fn new(base: usize) -> Self {
        Self {
            registers: unsafe { StaticRef::new(base as *const UartRegisters) },
        }
    }
}

impl Configuration<super::UartConfig> for Ns16650 {
    type Target = ();
    fn configure(&self, para: &super::UartConfig) -> blueos_hal::err::Result<()> {
        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Ns16650 {}

impl Has8bitDataReg for Ns16650 {
    fn read_data8(&self) -> Result<u8> {
        let er_bits = self.registers.ier.get();
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
        self.registers.rbr.set(data as u32);
    }

    fn is_data_ready(&self) -> bool {
        self.registers.lsr.is_set(LSR::DATA_READY)
    }
}

impl HasLineStatusReg for Ns16650 {
    fn is_bus_busy(&self) -> bool {
        !self.registers.lsr.is_set(LSR::TRANS_EMPTY)
    }
}

impl HasFifo for Ns16650 {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        todo!()
    }

    fn is_tx_fifo_full(&self) -> bool {
        !self.registers.lsr.is_set(LSR::TRANS_EMPTY)
    }

    fn is_rx_fifo_empty(&self) -> bool {
        !self.registers.lsr.is_set(LSR::DATA_READY)
    }
}

impl HasInterruptReg for Ns16650 {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, int_type: Self::InterruptType) {}

    fn disable_interrupt(&self, int_type: Self::InterruptType) {}

    fn clear_interrupt(&self, int_type: Self::InterruptType) {
        match int_type {
            super::InterruptType::Rx => {}
            super::InterruptType::Tx => {}
            _ => {}
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        todo!()
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {}

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

unsafe impl Sync for Ns16650 {}
unsafe impl Send for Ns16650 {}

impl PlatPeri for Ns16650 {
    fn enable(&self) {}

    fn disable(&self) {}
}
