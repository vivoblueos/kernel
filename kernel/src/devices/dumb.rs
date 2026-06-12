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

use crate::devices::tty::termios::Termios;
use core::fmt;
use embedded_io::{Error, ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};

/// Simple error type for the DumbUart implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SerialError;

impl Error for SerialError {
    fn kind(&self) -> ErrorKind {
        ErrorKind::Other
    }
}

impl fmt::Display for SerialError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SerialError")
    }
}

/// Trait defining UART operations needed for serial devices.
pub trait UartOps: ReadReady + WriteReady + ErrorType {
    fn setup(&mut self, termios: &Termios) -> Result<(), Self::Error>;
    fn shutdown(&mut self) -> Result<(), Self::Error>;
    fn read_byte(&mut self) -> Result<u8, Self::Error>;
    fn write_byte(&mut self, c: u8) -> Result<(), Self::Error>;
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error>;
    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), Self::Error>;
    fn set_rx_interrupt(&mut self, enable: bool);
    fn set_tx_interrupt(&mut self, enable: bool);
    fn clear_rx_interrupt(&mut self);
    fn clear_tx_interrupt(&mut self);
}

pub(crate) struct DumbUart;

unsafe impl Send for DumbUart {}
unsafe impl Sync for DumbUart {}

impl ErrorType for DumbUart {
    type Error = SerialError;
}

impl WriteReady for DumbUart {
    fn write_ready(&mut self) -> Result<bool, SerialError> {
        Ok(true)
    }
}

impl ReadReady for DumbUart {
    fn read_ready(&mut self) -> Result<bool, SerialError> {
        Ok(true)
    }
}

impl Read for DumbUart {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, SerialError> {
        Ok(buf.len())
    }
}

impl Write for DumbUart {
    fn write(&mut self, buf: &[u8]) -> Result<usize, SerialError> {
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), SerialError> {
        Ok(())
    }
}

impl UartOps for DumbUart {
    fn setup(&mut self, _: &Termios) -> Result<(), SerialError> {
        Ok(())
    }

    fn shutdown(&mut self) -> Result<(), SerialError> {
        Ok(())
    }

    fn read_byte(&mut self) -> Result<u8, SerialError> {
        Ok(0u8)
    }

    fn write_byte(&mut self, c: u8) -> Result<(), SerialError> {
        Ok(())
    }

    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        Ok(())
    }

    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), SerialError> {
        Ok(())
    }

    fn set_rx_interrupt(&mut self, enable: bool) {}

    fn set_tx_interrupt(&mut self, enable: bool) {}

    fn clear_rx_interrupt(&mut self) {}

    fn clear_tx_interrupt(&mut self) {}
}