// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/uart.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use crate::{
    arch::{self, irq::IrqNumber},
    boards::raspberry_pico2_cortexm::rp235x::static_ref::StaticRef,
    devices::tty::serial::{SerialError, UartOps},
    irq::IrqTrace,
};
use embedded_io::{ErrorType, Read, ReadReady, Write, WriteReady};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

register_structs! {
    /// controls serial port
    UartRegisters {
        (0x000 => uartdr: ReadWrite<u32, UARTDR::Register>),

        (0x004 => uartrsr: ReadWrite<u32, UARTRSR::Register>),
        (0x008 => _reserved0),

        (0x018 => uartfr: ReadOnly<u32, UARTFR::Register>),
        (0x01c => _reserved1),

        (0x020 => uartilpr: ReadWrite<u32, UARTILPR::Register>),

        (0x024 => uartibrd: ReadWrite<u32, UARTIBRD::Register>),

        (0x028 => uartfbrd: ReadWrite<u32, UARTFBRD::Register>),

        (0x02c => uartlcr_h: ReadWrite<u32, UARTLCR_H::Register>),

        (0x030 => uartcr: ReadWrite<u32, UARTCR::Register>),

        (0x034 => uartifls: ReadWrite<u32, UARTIFLS::Register>),

        (0x038 => uartimsc: ReadWrite<u32, UARTIMSC::Register>),

        (0x03c => uartris: ReadOnly<u32, UARTRIS::Register>),

        (0x040 => uartmis: ReadOnly<u32, UARTMIS::Register>),

        (0x044 => uarticr: ReadWrite<u32, UARTICR::Register>),

        (0x048 => uartdmacr: ReadWrite<u32, UARTDMACR::Register>),
        (0x04c => _reserved2),

        (0xfe0 => uartperiphid0: ReadOnly<u32, UARTPERIPHID0::Register>),

        (0xfe4 => uartperiphid1: ReadOnly<u32, UARTPERIPHID1::Register>),

        (0xfe8 => uartperiphid2: ReadOnly<u32, UARTPERIPHID2::Register>),

        (0xfec => uartperiphid3: ReadOnly<u32, UARTPERIPHID3::Register>),

        (0xff0 => uartpcellid0: ReadOnly<u32, UARTPCELLID0::Register>),

        (0xff4 => uartpcellid1: ReadOnly<u32, UARTPCELLID1::Register>),

        (0xff8 => uartpcellid2: ReadOnly<u32, UARTPCELLID2::Register>),

        (0xffc => uartpcellid3: ReadOnly<u32, UARTPCELLID3::Register>),

        (0x1000 => @END),
    }
}

register_bitfields! [u32,
    /// data register
    UARTDR [
        /// data bytes
        DATA OFFSET(0) NUMBITS(8) [],
        /// framing error
        FE OFFSET(8) NUMBITS(1) [],
        /// parity error
        PE OFFSET(9) NUMBITS(1) [],
        /// break error
        BE OFFSET(10) NUMBITS(1) [],
        /// overrun error
        OE OFFSET(11) NUMBITS(1) []
    ],
    /// receive status register/ error clear register
    UARTRSR [
        /// framing error
        FE OFFSET(0) NUMBITS(1) [],
        /// parity error
        PE OFFSET(1) NUMBITS(1) [],
        /// break error
        BE OFFSET(2) NUMBITS(1) [],
        /// overrun error
        OE OFFSET(3) NUMBITS(1) []
    ],
    /// flag register
    UARTFR  [
        /// clear to send
        CTS OFFSET(0) NUMBITS(1) [],
        /// data set ready
        DSR OFFSET(1) NUMBITS(1) [],
        /// data carrier detect
        DCD OFFSET(2) NUMBITS(1) [],
        /// busy
        BUSY OFFSET(3) NUMBITS(1) [],
        /// receive FIFO empty
        RXFE OFFSET(4) NUMBITS(1) [],
        /// transmit FIFO full
        TXFF OFFSET(5) NUMBITS(1) [],
        /// receive FIFO full
        RXFF OFFSET(6) NUMBITS(1) [],
        /// transmit FIFO empty
        TXFE OFFSET(7) NUMBITS(1) [],
        /// ring indicator
        RI OFFSET(8) NUMBITS(1) []
    ],
    /// IrDA low-power counter register
    UARTILPR [
        /// 8-bit low-power divisor value
        ILPDVSR OFFSET(0) NUMBITS(8) []
    ],
    /// integer baud rate register
    UARTIBRD [
        /// the integer baud rate divisor
        BAUD_DIVINT OFFSET(0) NUMBITS(16) []
    ],
    /// fractional baud rate register
    UARTFBRD [
        /// the fractional baud rate divisor
        BAUD_DIVFRAC OFFSET(0) NUMBITS(6) []
    ],
    /// line control register
    UARTLCR_H [
        /// send break
        BRK OFFSET(0) NUMBITS(1) [],
        /// parity enable
        PEN OFFSET(1) NUMBITS(1) [],
        /// even parity select
        EPS OFFSET(2) NUMBITS(1) [],
        /// two stop bits select
        STP2 OFFSET(3) NUMBITS(1) [],
        /// enable FIFOs
        FEN OFFSET(4) NUMBITS(1) [],
        /// word length
        WLEN OFFSET(5) NUMBITS(2) [
            BITS_8 = 0b11,
            BITS_7 = 0b10,
            BITS_6 = 0b01,
            BITS_5 = 0b00
        ],
        /// stick parity select
        SPS OFFSET(7) NUMBITS(1) []
    ],
    /// control register
    UARTCR [
        /// UART enable
        UARTEN OFFSET(0) NUMBITS(1) [],
        /// SIR enable
        SIREN OFFSET(1) NUMBITS(1) [],
        /// SIR low-power IrDA mode
        SIRLP OFFSET(2) NUMBITS(1) [],

        //RESERVED OFFSET(3) NUMBITS(3) [],
        /// loopback enable
        LBE OFFSET(7) NUMBITS(1) [],
        /// transmit enable
        TXE OFFSET(8) NUMBITS(1) [],
        /// receive enable
        RXE OFFSET(9) NUMBITS(1) [],
        /// data transmit ready
        DTR OFFSET(10) NUMBITS(1) [],
        /// request to send
        RTS OFFSET(11) NUMBITS(1) [],
        /// the complement of the UART Out1 (nUARTOut1) modem status output
        OUT1 OFFSET(12) NUMBITS(1) [],
        /// the complement of the UART Out2 (nUARTOut2) modem status output
        OUT2 OFFSET(13) NUMBITS(1) [],
        /// RTS hardware flow control enable
        RTSEN OFFSET(14) NUMBITS(1) [],
        /// CTS hardware flow control enable
        CTSEN OFFSET(15) NUMBITS(1) []
    ],
    /// interrupt FIFO level select register
    UARTIFLS [
        /// transmit interrupt FIFO level select
        TXIFLSEL OFFSET(0) NUMBITS(3) [
            FIFO_1_8 = 0b000,
            FIFO_1_4 = 0b001,
            FIFO_1_2 = 0b010,
            FIFO_3_4 = 0b011,
            FIFO_7_8 = 0b100,
        ],
        /// receive interrupt FIFO level select
        RXIFLSEL OFFSET(3) NUMBITS(3) [
            FIFO_1_8 = 0b000,
            FIFO_1_4 = 0b001,
            FIFO_1_2 = 0b010,
            FIFO_3_4 = 0b011,
            FIFO_7_8 = 0b100,
        ]
    ],

    /// interrupt mask set/clear register
    UARTIMSC [
        /// nUARTRI modem interrupt mask
        RIMIM OFFSET(0) NUMBITS(1) [],
        /// nUARTCTS modem interrupt mask
        CTSMIM OFFSET(1) NUMBITS(1) [],
        /// nUARTDCD modem interrupt mask
        DCDMIM OFFSET(2) NUMBITS(1) [],
        /// nUARTDSR modem interrupt mask
        DSRMIM OFFSET(3) NUMBITS(1) [],
        /// receive interrupt mask
        RXIM OFFSET(4) NUMBITS(1) [],
        /// transmit interrupt mask
        TXIM OFFSET(5) NUMBITS(1) [],
        /// receive timeout interrupt mask
        RTIM OFFSET(6) NUMBITS(1) [],
        /// framing error interrupt mask
        FEIM OFFSET(7) NUMBITS(1) [],
        /// parity error interrupt mask
        PEIM OFFSET(8) NUMBITS(1) [],
        /// break error interrupt mask
        BEIM OFFSET(9) NUMBITS(1) [],
        /// overrun error interrupt mask
        OEIM OFFSET(10) NUMBITS(1) []
    ],
    /// raw interrupt status register
    UARTRIS [
        /// nUARTRI modem interrupt status
        RIRMIS OFFSET(0) NUMBITS(1) [],
        /// nUARTCTS modem interrupt status
        CTSRMIS OFFSET(1) NUMBITS(1) [],
        /// nUARTDCD modem interrupt status
        DCDRMIS OFFSET(2) NUMBITS(1) [],
        /// nUARTDSR modem interrupt status
        DSRRMIS OFFSET(3) NUMBITS(1) [],
        /// receive interrupt status
        RXRIS OFFSET(4) NUMBITS(1) [],
        /// transmit interrupt status
        TXRIS OFFSET(5) NUMBITS(1) [],
        /// receive timeout interrupt status
        RTRIS OFFSET(6) NUMBITS(1) [],
        /// framing error interrupt status
        FERIS OFFSET(7) NUMBITS(1) [],
        /// parity error interrupt status
        PERIS OFFSET(8) NUMBITS(1) [],
        /// break error interrupt status
        BERIS OFFSET(9) NUMBITS(1) [],
        /// overrun error interrupt status
        OERIS OFFSET(10) NUMBITS(1) []
    ],
    /// masked interrupt status register
    UARTMIS [
        /// nUARTRI modem masked interrupt status
        RIMMIS OFFSET(0) NUMBITS(1) [],
        /// nUARTCTS modem masked interrupt status
        CTSMMIS OFFSET(1) NUMBITS(1) [],
        /// nUARTDCD modem masked interrupt status
        DCDMMIS OFFSET(2) NUMBITS(1) [],
        /// nUARTDSR modem masked interrupt status
        DSRMMIS OFFSET(3) NUMBITS(1) [],
        /// receive masked interrupt status
        RXMIS OFFSET(4) NUMBITS(1) [],
        /// transmit masked interrupt status
        TXMIS OFFSET(5) NUMBITS(1) [],
        /// receive timeout masked interrupt status
        RTMIS OFFSET(6) NUMBITS(1) [],
        /// framing error masked interrupt status
        FEMIS OFFSET(7) NUMBITS(1) [],
        /// parity error masked interrupt status
        PEMIS OFFSET(8) NUMBITS(1) [],
        /// break error masked interrupt status
        BEMIS OFFSET(9) NUMBITS(1) [],
        /// overrun error masked interrupt status
        OEMIS OFFSET(10) NUMBITS(1) []
    ],
    /// interrupt clear register
    UARTICR [
        /// nUARTRI modem interrupt clear
        RIMIC OFFSET(0) NUMBITS(1) [],
        /// nUARTCTS modem interrupt clear
        CTSMIC OFFSET(1) NUMBITS(1) [],
        /// nUARTDCD modem interrupt clear
        DCDMIC OFFSET(2) NUMBITS(1) [],
        /// nUARTDSR modem interrupt clear
        DSRMIC OFFSET(3) NUMBITS(1) [],
        /// receive interrupt clear
        RXIC OFFSET(4) NUMBITS(1) [],
        /// transmit interrupt clear
        TXIC OFFSET(5) NUMBITS(1) [],
        /// receive timeout interrupt clear
        RTIC OFFSET(6) NUMBITS(1) [],
        /// framing error interrupt clear
        FEIC OFFSET(7) NUMBITS(1) [],
        /// parity error interrupt clear
        PEIC OFFSET(8) NUMBITS(1) [],
        /// break error interrupt clear
        BEIC OFFSET(9) NUMBITS(1) [],
        /// overrun error interrupt clear
        OEIC OFFSET(10) NUMBITS(1) []
    ],
    /// DMA control register
    UARTDMACR [
        /// Receive DMA enable
        RXDMAE OFFSET(0) NUMBITS(1) [],
        /// transmit DMA enable
        TXDMAE OFFSET(1) NUMBITS(1) [],
        /// DMA on error
        DMAONERR OFFSET(2) NUMBITS(1) []
    ],
    /// UARTPeriphID0 register
    UARTPERIPHID0 [
        /// these bits read back as 0x11
        PARTNUMBER0 OFFSET(0) NUMBITS(8) []
    ],
    /// UARTPeriphID1 register
    UARTPERIPHID1 [
        /// these bits read back as 0x0
        PARTNUMBER1 OFFSET(0) NUMBITS(4) [],
        /// these bits read back as 0x1
        DESIGNER0 OFFSET(4) NUMBITS(4) []
    ],
    /// UARTPeriphID2 register
    UARTPERIPHID2 [
        /// these bits read back as 0x4
        DESIGNER1 OFFSET(0) NUMBITS(4) [],
        /// this field depends on the revision of the UART: r1p0 0x0 r1p1 0x1 r1p3 0x2 r1p4 0x2 r1p5 0x3
        REVISION OFFSET(4) NUMBITS(4) []
    ],
    /// UARTPeriphID3 register
    UARTPERIPHID3 [
        /// these bits read back as 0x00
        CONFIGURATION OFFSET(0) NUMBITS(8) []
    ],
    /// UARTPCellID0 register
    UARTPCELLID0 [
        /// these bits read back as 0x0D
        UARTPCELLID0 OFFSET(0) NUMBITS(8) []
    ],
    /// UARTPCellID1 register
    UARTPCELLID1 [
        /// these bits read back as 0xF0
        UARTPCELLID1 OFFSET(0) NUMBITS(8) []
    ],
    /// UARTPCellID2 register
    UARTPCELLID2 [
        /// these bits read back as 0x05
        UARTPCELLID2 OFFSET(0) NUMBITS(8) []
    ],
    /// UARTPCellID3 register
    UARTPCELLID3 [
        /// these bits read back as 0xB1
        UARTPCELLID3 OFFSET(0) NUMBITS(8) []
    ]
];

const UART0_BASE: StaticRef<UartRegisters> =
    unsafe { StaticRef::new(0x40070000 as *const UartRegisters) };

const UART1_BASE: StaticRef<UartRegisters> =
    unsafe { StaticRef::new(0x40078000 as *const UartRegisters) };

pub struct Uart {
    registers: StaticRef<UartRegisters>,
}

impl Uart {
    pub const fn new() -> Self {
        Self {
            registers: UART0_BASE,
        }
    }

    pub fn enable(&self, baud_rate: u32) {
        let clk = crate::boards::raspberry_pico2_cortexm::config::PLL_SYS_FREQ as u32;
        let baud_rate_div = 8 * clk / baud_rate;
        let mut baud_ibrd = baud_rate_div >> 7;
        let mut baud_fbrd = (baud_rate_div & 0x7f).div_ceil(2);

        if baud_ibrd == 0 {
            baud_ibrd = 1;
            baud_fbrd = 0;
        } else if baud_ibrd >= 65535 {
            baud_ibrd = 65535;
            baud_fbrd = 0;
        }

        self.registers
            .uartibrd
            .write(UARTIBRD::BAUD_DIVINT.val(baud_ibrd));
        self.registers
            .uartfbrd
            .write(UARTFBRD::BAUD_DIVFRAC.val(baud_fbrd));

        self.registers.uartlcr_h.write(UARTLCR_H::FEN::SET);

        self.registers.uartlcr_h.modify(UARTLCR_H::WLEN::BITS_8);

        self.registers.uartlcr_h.modify(UARTLCR_H::PEN::CLEAR);
        self.registers.uartlcr_h.modify(UARTLCR_H::STP2::CLEAR);

        self.registers
            .uartcr
            .modify(UARTCR::UARTEN::SET + UARTCR::TXE::SET + UARTCR::RXE::SET);

        self.registers
            .uartdmacr
            .write(UARTDMACR::TXDMAE::SET + UARTDMACR::RXDMAE::SET);
    }

    pub fn disable(&self) {
        self.registers.uartcr.modify(UARTCR::UARTEN::CLEAR);
    }

    pub fn is_tx_fifo_full(&self) -> bool {
        self.registers.uartfr.is_set(UARTFR::TXFF)
    }

    pub fn is_rx_fifo_full(&self) -> bool {
        self.registers.uartfr.is_set(UARTFR::RXFF)
    }

    #[inline]
    pub fn is_transmitting(&self) -> bool {
        self.registers.uartfr.is_set(UARTFR::BUSY)
    }

    #[inline]
    pub fn enable_tx_interrupt(&self) {
        self.registers.uartifls.modify(UARTIFLS::TXIFLSEL::FIFO_1_2);

        self.registers.uartimsc.modify(UARTIMSC::TXIM::SET);
    }

    #[inline]
    pub fn disable_tx_interrupt(&self) {
        self.registers.uartimsc.modify(UARTIMSC::TXIM::CLEAR);
    }

    #[inline]
    pub fn enable_rx_interrupt(&self) {
        self.registers
            .uartimsc
            .modify(UARTIMSC::RXIM::SET + UARTIMSC::RTIM::SET);
    }

    #[inline]
    pub fn disable_rx_interrupt(&self) {
        self.registers
            .uartimsc
            .modify(UARTIMSC::RTIM::CLEAR + UARTIMSC::RXIM::CLEAR);
    }

    #[inline]
    pub fn is_writable(&self) -> bool {
        !self.registers.uartfr.is_set(UARTFR::TXFF)
    }

    pub fn send_byte(&self, data: u8) {
        while !self.is_writable() {}
        self.registers.uartdr.write(UARTDR::DATA.val(data as u32));
    }

    pub fn read_data(&self) -> Result<Option<u8>, SerialError> {
        if self.registers.uartfr.is_set(UARTFR::RXFE) {
            return Ok(None); // No data available
        } else {
            let ch = self.registers.uartdr.read(UARTDR::DATA);
            self.registers.uartrsr.set(0); // Clear any errors
            return Ok(Some(ch as u8));
        }
    }
}

unsafe impl Send for Uart {}
unsafe impl Sync for Uart {}

impl Drop for Uart {
    fn drop(&mut self) {
        self.disable();
    }
}

impl ErrorType for Uart {
    type Error = SerialError;
}

impl Write for Uart {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let mut count = 0;
        for &byte in buf {
            self.send_byte(byte);
            count += 1;
        }
        Ok(count)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        while self.is_transmitting() {}
        Ok(())
    }
}

impl WriteReady for Uart {
    fn write_ready(&mut self) -> Result<bool, Self::Error> {
        Ok(!self.registers.uartfr.is_set(UARTFR::TXFF))
    }
}

impl Read for Uart {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut count = 0;
        while count < buf.len() {
            match self.read_data() {
                Ok(Some(byte)) => {
                    buf[count] = byte;
                    count += 1;
                }
                Ok(_) => break,          // No more data available
                Err(e) => return Err(e), // Error occurred
            }
        }

        Ok(count)
    }
}

impl ReadReady for Uart {
    fn read_ready(&mut self) -> Result<bool, Self::Error> {
        Ok(!self.registers.uartfr.is_set(UARTFR::RXFE))
    }
}

impl UartOps for Uart {
    fn setup(
        &mut self,
        termios: &crate::devices::tty::termios::Termios,
    ) -> Result<(), SerialError> {
        self.enable(termios.getospeed());
        crate::arch::irq::enable_irq_with_priority(
            arch::irq::IrqNumber::new(33),
            arch::irq::Priority::Normal,
        );

        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), SerialError> {
        crate::arch::irq::disable_irq(arch::irq::IrqNumber::new(33));
        self.disable();
        Ok(())
    }

    fn read_byte(&mut self) -> Result<u8, SerialError> {
        match self.read_data()? {
            Some(byte) => Ok(byte),
            _ => Err(SerialError::BufferEmpty),
        }
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), SerialError> {
        self.send_byte(byte);
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        for c in s.as_bytes() {
            self.send_byte(*c);
        }
        Ok(())
    }

    fn set_rx_interrupt(&mut self, enable: bool) {
        if enable {
            self.enable_rx_interrupt();
        } else {
            self.disable_rx_interrupt();
        }
    }

    fn set_tx_interrupt(&mut self, enable: bool) {
        if enable {
            self.enable_tx_interrupt();
        } else {
            self.disable_tx_interrupt();
        }
    }

    fn clear_rx_interrupt(&mut self) {
        // self.inner_clear_rx_interrupt();
        self.registers.uarticr.modify(UARTICR::RXIC::SET);
        self.registers.uarticr.modify(UARTICR::RTIC::SET);
    }

    fn clear_tx_interrupt(&mut self) {
        // self.inner_clear_tx_interrupt();
        self.registers.uarticr.modify(UARTICR::TXIC::SET);
    }

    fn ioctl(&mut self, _request: u32, _arg: usize) -> Result<(), SerialError> {
        Ok(())
    }
}

#[coverage(off)]
pub unsafe extern "C" fn uart0_handler() {
    let _ = IrqTrace::new(IrqNumber::new(33));
    if UART0_BASE.uartimsc.is_set(UARTIMSC::TXIM) {
        if UART0_BASE.uartfr.is_set(UARTFR::TXFE) {
            let uart = crate::boards::raspberry_pico2_cortexm::SERIAL0
                .get()
                .unwrap();
            uart.uart_ops.irqsave_lock().clear_tx_interrupt();
            if let Err(_e) = uart.xmitchars() {}
        }
    }

    if UART0_BASE.uartimsc.is_set(UARTIMSC::RXIM) {
        if UART0_BASE.uartfr.is_set(UARTFR::RXFE) {
            let uart = crate::boards::raspberry_pico2_cortexm::SERIAL0
                .get()
                .unwrap();
            uart.uart_ops.irqsave_lock().clear_rx_interrupt();
            if let Err(_e) = uart.recvchars() {
                // println!("UART RX error: {:?}", e);
            }
        }
    }
}
