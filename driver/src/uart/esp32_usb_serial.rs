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

use crate::static_ref::StaticRef;
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

    pub EP1_REG [
        RDWR_BYTE OFFSET(0) NUMBITS(8) []
    ],

    pub EP1_CONF_REG [
        WR_DONE OFFSET(0) NUMBITS(1) [],
        IN_EP_DATA_FREE OFFSET(1) NUMBITS(1) [
            FREE = 1,
            NOT_FREE = 0
        ],
        OUT_EP_DATA_AVAIL OFFSET(2) NUMBITS(1) [
            AVAIL = 1,
            NOT_AVAIL = 0
        ]
    ],

    pub JFIFO_ST_REG [
        IN_FIFO_CNT OFFSET(0) NUMBITS(2) [],
        IN_FIFO_EMPTY OFFSET(2) NUMBITS(1) [
            EMPTY = 1,
            NOT_EMPTY = 0
        ],
        IN_FIFO_FULL OFFSET(3) NUMBITS(1) [
            FULL = 1,
            NOT_FULL = 0
        ],
        OUT_FIFO_CNT OFFSET(4) NUMBITS(2) [],
        OUT_FIFO_EMPTY OFFSET(6) NUMBITS(1) [
            EMPTY = 1,
            NOT_EMPTY = 0
        ],
        OUT_FIFO_FULL OFFSET(7) NUMBITS(1) [
            FULL = 1,
            NOT_FULL = 0
        ],
        IN_FIFO_RESET OFFSET(8) NUMBITS(1) [],
        OUT_FIFO_RESET OFFSET(9) NUMBITS(1) []
    ]
];

register_structs! {
    Registers {
        (0x00 => ep1_reg: ReadWrite<u32, EP1_REG::Register>),
        (0x04 => ep1_conf_reg: ReadWrite<u32, EP1_CONF_REG::Register>),
        (0x08 => _reserved0),
        (0x20 => jfifo_st_reg: ReadWrite<u32, JFIFO_ST_REG::Register>),
        (0x24 => @END),
    }
}

const USB_SERIAL_BASE: StaticRef<Registers> =
    unsafe { StaticRef::new(0x6004_3000 as *const Registers) };

pub struct Esp32UsbSerial;

unsafe impl Send for Esp32UsbSerial {}
unsafe impl Sync for Esp32UsbSerial {}

impl Configuration<super::UartConfig> for Esp32UsbSerial {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        Ok(())
    }
}

impl Has8bitDataReg for Esp32UsbSerial {
    fn write_data8(&self, data: u8) {
        USB_SERIAL_BASE
            .ep1_reg
            .write(EP1_REG::RDWR_BYTE.val(data as u32));
        USB_SERIAL_BASE
            .ep1_conf_reg
            .write(EP1_CONF_REG::WR_DONE.val(1));
    }

    fn is_data_ready(&self) -> bool {
        USB_SERIAL_BASE
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::OUT_EP_DATA_AVAIL)
    }

    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        Ok(USB_SERIAL_BASE.ep1_reg.read(EP1_REG::RDWR_BYTE) as u8)
    }
}

impl HasLineStatusReg for Esp32UsbSerial {
    fn is_bus_busy(&self) -> bool {
        USB_SERIAL_BASE
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::IN_EP_DATA_FREE)
            != true
    }
}

impl HasFifo for Esp32UsbSerial {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        // USB_SERIAL_BASE
        //     .jfifo_st_reg
        //     .is_set(JFIFO_ST_REG::IN_FIFO_FULL)
        USB_SERIAL_BASE
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::IN_EP_DATA_FREE)
            != true
    }

    fn is_rx_fifo_empty(&self) -> bool {
        USB_SERIAL_BASE
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::OUT_EP_DATA_AVAIL)
            != true
    }
}

impl HasInterruptReg for Esp32UsbSerial {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        // Not supported
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        // Not supported
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        // Not supported
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        super::InterruptType::Unknown
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {
        // Not supported
    }

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

impl PlatPeri for Esp32UsbSerial {}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Esp32UsbSerial {}
