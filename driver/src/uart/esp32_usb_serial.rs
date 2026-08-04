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
    isr::IsrDesc, uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg,
    HasLineStatusReg, PlatPeri,
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
    ],

    pub INT_ENA_REG [
        JTAG_IN_FLUSH OFFSET(0) NUMBITS(1) [],
        SOF OFFSET(1) NUMBITS(1) [],
        SERIAL_OUT_RECV_PKT OFFSET(2) NUMBITS(1) [],
        SERIAL_IN_EMPTY OFFSET(3) NUMBITS(1) [],
        PID_ERR OFFSET(4) NUMBITS(1) [],
        CRC5_ERR OFFSET(5) NUMBITS(1) [],
        CRC16_ERR OFFSET(6) NUMBITS(1) [],
        STUFF_ERR OFFSET(7) NUMBITS(1) [],
        IN_TOKEN_REC_IN_EP1 OFFSET(8) NUMBITS(1) [],
        USB_BUS_RESET OFFSET(9) NUMBITS(1) [],
        OUT_EP1_ZERO_PAYLOAD OFFSET(10) NUMBITS(1) [],
        OUT_EP2_ZERO_PAYLOAD OFFSET(11) NUMBITS(1) []
    ],

    pub INT_RAW_REG [
        JTAG_IN_FLUSH OFFSET(0) NUMBITS(1) [],
        SOF OFFSET(1) NUMBITS(1) [],
        SERIAL_OUT_RECV_PKT OFFSET(2) NUMBITS(1) [],
        SERIAL_IN_EMPTY OFFSET(3) NUMBITS(1) [],
        PID_ERR OFFSET(4) NUMBITS(1) [],
        CRC5_ERR OFFSET(5) NUMBITS(1) [],
        CRC16_ERR OFFSET(6) NUMBITS(1) [],
        STUFF_ERR OFFSET(7) NUMBITS(1) [],
        IN_TOKEN_REC_IN_EP1 OFFSET(8) NUMBITS(1) [],
        USB_BUS_RESET OFFSET(9) NUMBITS(1) [],
        OUT_EP1_ZERO_PAYLOAD OFFSET(10) NUMBITS(1) [],
        OUT_EP2_ZERO_PAYLOAD OFFSET(11) NUMBITS(1) []
    ],

    pub INT_ST_REG [
        JTAG_IN_FLUSH OFFSET(0) NUMBITS(1) [],
        SOF OFFSET(1) NUMBITS(1) [],
        SERIAL_OUT_RECV_PKT OFFSET(2) NUMBITS(1) [],
        SERIAL_IN_EMPTY OFFSET(3) NUMBITS(1) [],
        PID_ERR OFFSET(4) NUMBITS(1) [],
        CRC5_ERR OFFSET(5) NUMBITS(1) [],
        CRC16_ERR OFFSET(6) NUMBITS(1) [],
        STUFF_ERR OFFSET(7) NUMBITS(1) [],
        IN_TOKEN_REC_IN_EP1 OFFSET(8) NUMBITS(1) [],
        USB_BUS_RESET OFFSET(9) NUMBITS(1) [],
        OUT_EP1_ZERO_PAYLOAD OFFSET(10) NUMBITS(1) [],
        OUT_EP2_ZERO_PAYLOAD OFFSET(11) NUMBITS(1) []
    ],

    pub INT_CLR_REG [
        JTAG_IN_FLUSH OFFSET(0) NUMBITS(1) [],
        SOF OFFSET(1) NUMBITS(1) [],
        SERIAL_OUT_RECV_PKT OFFSET(2) NUMBITS(1) [],
        SERIAL_IN_EMPTY OFFSET(3) NUMBITS(1) [],
        PID_ERR OFFSET(4) NUMBITS(1) [],
        CRC5_ERR OFFSET(5) NUMBITS(1) [],
        CRC16_ERR OFFSET(6) NUMBITS(1) [],
        STUFF_ERR OFFSET(7) NUMBITS(1) [],
        IN_TOKEN_REC_IN_EP1 OFFSET(8) NUMBITS(1) [],
        USB_BUS_RESET OFFSET(9) NUMBITS(1) [],
        OUT_EP1_ZERO_PAYLOAD OFFSET(10) NUMBITS(1) [],
        OUT_EP2_ZERO_PAYLOAD OFFSET(11) NUMBITS(1) []
    ]
];

register_structs! {
    Registers {
        (0x00 => ep1_reg: ReadWrite<u32, EP1_REG::Register>),
        (0x04 => ep1_conf_reg: ReadWrite<u32, EP1_CONF_REG::Register>),
        (0x08 => int_raw_reg: ReadWrite<u32, INT_RAW_REG::Register>),
        (0x0c => int_st_reg: ReadWrite<u32, INT_ST_REG::Register>),
        (0x10 => int_ena_reg: ReadWrite<u32, INT_ENA_REG::Register>),
        (0x14 => int_clr_reg: ReadWrite<u32, INT_CLR_REG::Register>),
        (0x18 => _reserved1),
        (0x20 => jfifo_st_reg: ReadWrite<u32, JFIFO_ST_REG::Register>),
        (0x24 => @END),
    }
}

pub struct Esp32UsbSerial<const BASE: usize> {}

unsafe impl<const BASE: usize> Send for Esp32UsbSerial<BASE> {}
unsafe impl<const BASE: usize> Sync for Esp32UsbSerial<BASE> {}

impl<const BASE: usize> Esp32UsbSerial<BASE> {
    /// Returns a `StaticRef` to the register block at `BASE`.
    #[inline]
    const fn regs() -> StaticRef<Registers> {
        unsafe { StaticRef::new(BASE as *const Registers) }
    }

    pub const fn new() -> Self {
        Self {}
    }
}

impl<const BASE: usize> Configuration<super::UartConfig> for Esp32UsbSerial<BASE> {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        Ok(())
    }
}

impl<const BASE: usize> Has8bitDataReg for Esp32UsbSerial<BASE> {
    fn write_data8(&self, data: u8) {
        Self::regs()
            .ep1_reg
            .write(EP1_REG::RDWR_BYTE.val(data as u32));
    }

    fn is_data_ready(&self) -> bool {
        Self::regs()
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::OUT_EP_DATA_AVAIL)
    }

    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        Ok(Self::regs().ep1_reg.read(EP1_REG::RDWR_BYTE) as u8)
    }
}

impl<const BASE: usize> HasLineStatusReg for Esp32UsbSerial<BASE> {
    fn is_bus_busy(&self) -> bool {
        Self::regs()
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::IN_EP_DATA_FREE)
            != true
    }
}

impl<const BASE: usize> HasFifo for Esp32UsbSerial<BASE> {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        // Self::regs()
        //     .jfifo_st_reg
        //     .is_set(JFIFO_ST_REG::IN_FIFO_FULL)
        Self::regs()
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::IN_EP_DATA_FREE)
            != true
    }

    fn is_rx_fifo_empty(&self) -> bool {
        Self::regs()
            .ep1_conf_reg
            .is_set(EP1_CONF_REG::OUT_EP_DATA_AVAIL)
            != true
    }

    fn flush_tx_fifo(&self) {
        Self::regs()
            .ep1_conf_reg
            .write(EP1_CONF_REG::WR_DONE.val(1));
    }
}

impl<const BASE: usize> HasInterruptReg for Esp32UsbSerial<BASE> {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => {
                Self::regs()
                    .int_ena_reg
                    .modify(INT_ENA_REG::SERIAL_OUT_RECV_PKT::SET);
            }
            super::InterruptType::Tx => {
                Self::regs()
                    .int_ena_reg
                    .modify(INT_ENA_REG::SERIAL_IN_EMPTY::SET);
            }
            _ => {}
        }
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Tx => {
                Self::regs()
                    .int_ena_reg
                    .modify(INT_ENA_REG::SERIAL_IN_EMPTY::CLEAR);
            }
            super::InterruptType::Rx => {
                Self::regs()
                    .int_ena_reg
                    .modify(INT_ENA_REG::SERIAL_OUT_RECV_PKT::CLEAR);
            }
            _ => {}
        }
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => {
                Self::regs()
                    .int_clr_reg
                    .write(INT_CLR_REG::SERIAL_OUT_RECV_PKT::SET);
            }
            super::InterruptType::Tx => {
                Self::regs()
                    .int_clr_reg
                    .write(INT_CLR_REG::SERIAL_IN_EMPTY::SET);
            }
            super::InterruptType::All => {
                Self::regs().int_clr_reg.write(
                    INT_CLR_REG::SERIAL_OUT_RECV_PKT::SET + INT_CLR_REG::SERIAL_IN_EMPTY::SET,
                );
            }
            _ => {}
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        let status = &Self::regs().int_st_reg;
        let rx = status.is_set(INT_ST_REG::SERIAL_OUT_RECV_PKT);
        let tx = status.is_set(INT_ST_REG::SERIAL_IN_EMPTY);

        match (rx, tx) {
            (true, true) => super::InterruptType::All,
            (true, false) => super::InterruptType::Rx,
            (false, true) => super::InterruptType::Tx,
            _ => super::InterruptType::Unknown,
        }
    }

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

impl<const BASE: usize> PlatPeri for Esp32UsbSerial<BASE> {}

impl<const BASE: usize> Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus>
    for Esp32UsbSerial<BASE> {}

pub struct Esp32UsbSerialIsr<const DEVICE_ADDRESS: usize, T: Sync + 'static> {
    pub data: &'static T,
    pub rx_isr: Option<fn(&T)>,
    pub tx_isr: Option<fn(&T)>,
}

impl<const DEVICE_ADDRESS: usize, T: Sync> Esp32UsbSerialIsr<DEVICE_ADDRESS, T> {
    pub const fn new(data: &'static T, rx_isr: Option<fn(&T)>, tx_isr: Option<fn(&T)>) -> Self {
        Self {
            data,
            rx_isr,
            tx_isr,
        }
    }
}

impl<const DEVICE_ADDRESS: usize, T: Sync> IsrDesc for Esp32UsbSerialIsr<DEVICE_ADDRESS, T> {
    fn service_isr(&self) {
        let uart = unsafe { &*(DEVICE_ADDRESS as *const Esp32UsbSerial<DEVICE_ADDRESS>) };
        let intr = uart.get_interrupt();
        match intr {
            super::InterruptType::Rx => {
                uart.clear_interrupt(intr);
                if let Some(rx_isr) = self.rx_isr {
                    rx_isr(self.data);
                }
            }
            super::InterruptType::Tx => {
                uart.clear_interrupt(intr);
                if let Some(tx_isr) = self.tx_isr {
                    tx_isr(self.data);
                }
            }
            _ => {}
        }
    }
}
