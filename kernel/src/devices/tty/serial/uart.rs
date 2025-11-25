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

use crate::devices::{
    tty::{
        serial::UartOps,
        termios::{Cflags, Termios},
    },
    DeviceRequest,
};
use blueos_driver::uart::{InterruptType, UartCtrlStatus};
use blueos_hal::{uart::Uart, HasInterruptReg, PlatPeri};
use embedded_io::{ErrorType, Read, ReadReady, Write, WriteReady};

pub struct UartDevice<T: PlatPeri> {
    uart: &'static T,
}

unsafe impl<T> Send for UartDevice<T> where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >
{
}

unsafe impl<T> Sync for UartDevice<T> where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >
{
}

impl<T> ErrorType for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    type Error = super::SerialError;
}

impl<T> UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    pub fn new(uart: &'static T) -> Self {
        UartDevice { uart }
    }
}

impl From<blueos_hal::err::HalError> for super::SerialError {
    fn from(value: blueos_hal::err::HalError) -> Self {
        match value {
            blueos_hal::err::HalError::InvalidParam => super::SerialError::InvalidParameter,
            blueos_hal::err::HalError::Timeout => super::SerialError::TimedOut,
            blueos_hal::err::HalError::Other(s) => match s {
                "Overrun Error" => super::SerialError::Overrun,
                "Break Error" => super::SerialError::Break,
                "Parity Error" => super::SerialError::Parity,
                "Framing Error" => super::SerialError::Framing,
                _ => super::SerialError::DeviceError,
            },
            _ => super::SerialError::DeviceError,
        }
    }
}

impl<T> Write for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let mut count = 0;
        // write until the buffer is full
        while count < buf.len() {
            if self.uart.is_tx_fifo_full() {
                continue;
            }
            self.uart.write_data8(buf[count]);
            count += 1;
        }
        Ok(count)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        while self.uart.is_bus_busy() {}
        Ok(())
    }
}

impl<T> WriteReady for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    fn write_ready(&mut self) -> Result<bool, Self::Error> {
        Ok(!self.uart.is_tx_fifo_full())
    }
}

impl<T> Read for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            return Ok(0);
        }

        let mut count = 0;

        while count < buf.len() {
            match self.read_byte() {
                Ok(byte) => {
                    buf[count] = byte;
                    count += 1;
                }
                Err(super::SerialError::BufferEmpty) => break,
                Err(e) => return Err(e),
            }
        }

        Ok(count)
    }
}

impl<T> ReadReady for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    fn read_ready(&mut self) -> Result<bool, Self::Error> {
        Ok(!self.uart.is_rx_fifo_empty())
    }
}

impl<T> super::UartOps for UartDevice<T>
where
    T: blueos_hal::uart::Uart<
        blueos_driver::uart::UartConfig,
        (),
        blueos_driver::uart::InterruptType,
        blueos_driver::uart::UartCtrlStatus,
    >,
{
    fn setup(
        &mut self,
        termios: &crate::devices::tty::termios::Termios,
    ) -> Result<(), super::SerialError> {
        let config = blueos_driver::uart::UartConfig {
            baudrate: termios.getospeed(),
            data_bits: if termios.cflag.contains(Cflags::CSIZE_8) {
                blueos_driver::uart::DataBits::DataBits8
            } else if termios.cflag.contains(Cflags::CSIZE_7) {
                blueos_driver::uart::DataBits::DataBits7
            } else if termios.cflag.contains(Cflags::CSIZE_6) {
                blueos_driver::uart::DataBits::DataBits6
            } else {
                blueos_driver::uart::DataBits::DataBits5
            },
            parity: if !termios.cflag.contains(Cflags::PARENB) {
                blueos_driver::uart::Parity::None
            } else if termios.cflag.contains(Cflags::PARODD) {
                blueos_driver::uart::Parity::Odd
            } else {
                blueos_driver::uart::Parity::Even
            },
            stop_bits: if termios.cflag.contains(Cflags::CSTOPB) {
                blueos_driver::uart::StopBits::DataBits2
            } else {
                blueos_driver::uart::StopBits::DataBits1
            },
            flow_ctrl: blueos_driver::uart::FlowCtrl::None,
        };

        self.uart.clear_interrupt(InterruptType::All);
        self.uart.set_interrupt_handler(&uart_handler);
        self.uart.configure(&config)?;
        self.uart.enable();

        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), super::SerialError> {
        self.uart.disable();
        Ok(())
    }

    fn read_byte(&mut self) -> Result<u8, super::SerialError> {
        if self.uart.is_rx_fifo_empty() {
            return Err(super::SerialError::BufferEmpty);
        }

        let d = self.uart.read_data8()?;

        Ok(d)
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), super::SerialError> {
        self.uart.write_data8(byte);
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<(), super::SerialError> {
        for c in s.as_bytes() {
            while self.uart.is_tx_fifo_full() {}
            self.uart.write_data8(*c);
        }
        Ok(())
    }

    fn set_rx_interrupt(&mut self, enable: bool) {
        if enable {
            self.uart
                .enable_interrupt(blueos_driver::uart::InterruptType::Rx);
        } else {
            self.uart
                .disable_interrupt(blueos_driver::uart::InterruptType::Rx);
        }
    }

    fn set_tx_interrupt(&mut self, enable: bool) {
        if enable {
            self.uart
                .enable_interrupt(blueos_driver::uart::InterruptType::Tx);
        } else {
            self.uart
                .disable_interrupt(blueos_driver::uart::InterruptType::Tx);
        }
    }

    fn clear_rx_interrupt(&mut self) {
        self.uart
            .clear_interrupt(blueos_driver::uart::InterruptType::Rx);
    }

    fn clear_tx_interrupt(&mut self) {
        self.uart
            .clear_interrupt(blueos_driver::uart::InterruptType::Tx);
    }

    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), super::SerialError> {
        match DeviceRequest::from(request) {
            DeviceRequest::Config => {
                let termios = unsafe { *(arg as *const Termios) };
                self.setup(&termios)?;
                self.uart.enable();
            }
            DeviceRequest::Close => {
                self.uart.disable();
            }
            _ => return Err(super::SerialError::InvalidParameter),
        }
        Ok(())
    }
}

pub fn uart_handler() {
    let uart = crate::boards::get_device!(console_uart);
    let intr = uart.get_interrupt();
    match intr {
        blueos_driver::uart::InterruptType::Rx => {
            let t_uart = crate::boot::get_serial(0);
            if let Err(e) = t_uart.recvchars() {
                log::warn!("uart recvchars error: {:?}", e);
            }
        }
        blueos_driver::uart::InterruptType::Tx => {
            let t_uart = crate::boot::get_serial(0);
            if let Err(e) = t_uart.xmitchars() {
                log::warn!("uart xmitchars error: {:?}", e);
            }
        }
        _ => {}
    }
    uart.clear_interrupt(intr);
}
