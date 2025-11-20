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

pub mod uart;
use crate::{
    devices::{
        tty::termios::{CcIndex, Cflags, Iflags, Lflags, Oflags, Termios},
        Device, DeviceBase, DeviceClass, DeviceId, DeviceRequest,
    },
    irq, scheduler,
    sync::{
        atomic_wait::{atomic_wait, atomic_wake},
        spinlock::SpinLock,
    },
    time,
    types::RwLock,
};
use alloc::{format, string::String, sync::Arc};
use blueos_infra::ringbuffer::BoxedRingBuffer;
use blueos_kconfig::{
    CONFIG_SERIAL_RX_FIFO_SIZE as SERIAL_RX_FIFO_SIZE,
    CONFIG_SERIAL_TX_FIFO_SIZE as SERIAL_TX_FIFO_SIZE,
};
use core::sync::atomic::AtomicUsize;
use delegate::delegate;
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use libc::{
    c_int, TCFLSH, TCGETS, TCIFLUSH, TCIOFF, TCIOFLUSH, TCION, TCOFLUSH, TCOOFF, TCOON, TCSBRK,
    TCSETS, TCSETSF, TCSETSW, TCXONC,
};

const SERIAL_RX_FIFO_MIN_SIZE: u32 = 256;
const SERIAL_TX_FIFO_MIN_SIZE: u32 = 256;
const DEFAULT_BREAK_DURATION_MS: usize = 250;
const BREAK_UNIT_IN_MS: usize = 100;

#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum SerialError {
    #[error("Overrun")]
    Overrun,
    #[error("Break")]
    Break,
    #[error("Parity")]
    Parity,
    #[error("Framing")]
    Framing,
    #[error("Buffer is empty")]
    BufferEmpty,
    #[error("Device error")]
    DeviceError,
    #[error("Invalid configuration")]
    InvalidParameter,
    #[error("Operation timed out")]
    TimedOut,
}

impl embedded_io::Error for SerialError {
    fn kind(&self) -> ErrorKind {
        match self {
            Self::Break | Self::Overrun => ErrorKind::Other,
            Self::Framing | Self::Parity => ErrorKind::InvalidData,
            Self::BufferEmpty | Self::InvalidParameter => ErrorKind::InvalidInput,
            Self::DeviceError => ErrorKind::Other,
            Self::TimedOut => ErrorKind::TimedOut,
        }
    }
}

impl From<SerialError> for ErrorKind {
    fn from(error: SerialError) -> Self {
        match error {
            SerialError::Break | SerialError::Overrun => ErrorKind::Other,
            SerialError::Framing | SerialError::Parity => ErrorKind::InvalidData,
            SerialError::BufferEmpty | SerialError::InvalidParameter => ErrorKind::InvalidInput,
            SerialError::DeviceError => ErrorKind::Other,
            SerialError::TimedOut => ErrorKind::TimedOut,
        }
    }
}

// TODO: add DMA support
pub trait UartOps:
    Read
    + Write
    + ReadReady
    + WriteReady
    + ErrorType<Error = SerialError>
    + core::marker::Send
    + core::marker::Sync
{
    fn setup(&mut self, termios: &Termios) -> Result<(), SerialError>;
    fn shutdown(&mut self) -> Result<(), SerialError>;
    fn read_byte(&mut self) -> Result<u8, SerialError>;
    fn write_byte(&mut self, byte: u8) -> Result<(), SerialError>;
    fn write_str(&mut self, s: &str) -> Result<(), SerialError>;
    fn ioctl(&mut self, request: u32, arg: usize) -> Result<(), SerialError>;
    fn set_rx_interrupt(&mut self, enable: bool);
    fn set_tx_interrupt(&mut self, enable: bool);
    fn clear_rx_interrupt(&mut self);
    fn clear_tx_interrupt(&mut self);
    fn set_break(&mut self, enable: bool) -> Result<(), SerialError>;
}

#[derive(Debug)]
struct SerialRxFifo {
    rb: BoxedRingBuffer,
    futex: AtomicUsize,
}

#[derive(Debug)]
struct SerialTxFifo {
    rb: BoxedRingBuffer,
    futex: AtomicUsize,
}

impl SerialRxFifo {
    fn new(size: usize) -> Self {
        Self {
            rb: BoxedRingBuffer::new(size),
            futex: AtomicUsize::new(0),
        }
    }
}

impl SerialTxFifo {
    fn new(size: usize) -> Self {
        Self {
            rb: BoxedRingBuffer::new(size),
            futex: AtomicUsize::new(0),
        }
    }
}

pub struct Serial {
    base: DeviceBase,
    index: u32,
    termios: RwLock<Termios>,
    rx_fifo: SerialRxFifo,
    tx_fifo: SerialTxFifo,
    pub uart_ops: Arc<SpinLock<dyn UartOps>>,
}

impl Serial {
    pub fn new(index: u32, termios: Termios, uart_ops: Arc<SpinLock<dyn UartOps>>) -> Self {
        Self {
            base: DeviceBase::new(),
            index,
            termios: RwLock::new(termios),
            rx_fifo: SerialRxFifo::new(SERIAL_RX_FIFO_SIZE.max(SERIAL_RX_FIFO_MIN_SIZE) as usize),
            tx_fifo: SerialTxFifo::new(SERIAL_TX_FIFO_SIZE.max(SERIAL_TX_FIFO_MIN_SIZE) as usize),
            uart_ops,
        }
    }

    pub fn termios_snapshot(&self) -> Termios {
        *self.termios.read()
    }

    pub(crate) fn apply_termios(&self, new_termios: Termios) -> Result<(), ErrorKind> {
        {
            let mut guard = self.termios.write();
            *guard = new_termios;
        }

        let snapshot = self.termios_snapshot();
        let mut uart_ops = self.uart_ops.irqsave_lock();
        uart_ops.setup(&snapshot).map_err(ErrorKind::from)?;
        uart_ops.set_rx_interrupt(true);
        Ok(())
    }

    pub(crate) fn wait_for_tx_empty(&self) -> Result<(), ErrorKind> {
        loop {
            self.xmitchars().map_err(ErrorKind::from)?;
            if self.tx_fifo.rb.is_empty() {
                break;
            }
        }
        let mut uart_ops = self.uart_ops.irqsave_lock();
        uart_ops.flush().map_err(ErrorKind::from)
    }

    fn flush_rx_fifo(&self) {
        let _guard = self.uart_ops.irqsave_lock();
        unsafe {
            let mut reader = self.rx_fifo.rb.reader();
            while !reader.is_empty() {
                let slices = reader.pop_slices();
                let len = slices[0].len() + slices[1].len();
                if len == 0 {
                    break;
                }
                reader.pop_done(len);
            }
        }
        let _ = atomic_wake(&self.rx_fifo.futex, usize::MAX);
    }

    fn flush_tx_fifo(&self) {
        let _guard = self.uart_ops.irqsave_lock();
        unsafe {
            let mut reader = self.tx_fifo.rb.reader();
            while !reader.is_empty() {
                let slices = reader.pop_slices();
                let len = slices[0].len() + slices[1].len();
                if len == 0 {
                    break;
                }
                reader.pop_done(len);
            }
        }
        let _ = atomic_wake(&self.tx_fifo.futex, usize::MAX);
    }

    fn send_control_char(&self, ch: u8) -> Result<(), ErrorKind> {
        let mut uart_ops = self.uart_ops.irqsave_lock();
        uart_ops.write_byte(ch).map_err(ErrorKind::from)
    }

    fn send_break_signal(&self, duration: c_int) -> Result<(), ErrorKind> {
        if duration < 0 {
            return Err(ErrorKind::InvalidInput);
        }
        let interval_ms = if duration == 0 {
            DEFAULT_BREAK_DURATION_MS
        } else {
            (duration as usize).saturating_mul(BREAK_UNIT_IN_MS)
        };

        self.wait_for_tx_empty()?;

        {
            let mut uart_ops = self.uart_ops.irqsave_lock();
            uart_ops.set_break(true).map_err(ErrorKind::from)?;
        }

        scheduler::suspend_me_for(time::tick_from_millisecond(interval_ms));

        let mut uart_ops = self.uart_ops.irqsave_lock();
        uart_ops.set_break(false).map_err(ErrorKind::from)
    }

    pub(crate) fn handle_tcflsh(&self, action: c_int) -> Result<(), ErrorKind> {
        match action {
            TCIFLUSH => {
                self.flush_rx_fifo();
                Ok(())
            }
            TCOFLUSH => {
                self.flush_tx_fifo();
                Ok(())
            }
            TCIOFLUSH => {
                self.flush_rx_fifo();
                self.flush_tx_fifo();
                Ok(())
            }
            _ => Err(ErrorKind::InvalidInput),
        }
    }

    pub(crate) fn handle_tcxonc(&self, action: c_int) -> Result<(), ErrorKind> {
        match action {
            TCOOFF => {
                let mut uart_ops = self.uart_ops.irqsave_lock();
                uart_ops.set_tx_interrupt(false);
                Ok(())
            }
            TCOON => {
                let mut uart_ops = self.uart_ops.irqsave_lock();
                uart_ops.set_tx_interrupt(true);
                drop(uart_ops);
                self.xmitchars().map_err(ErrorKind::from)?;
                Ok(())
            }
            TCIOFF => {
                let cc = self.termios.read().cc;
                self.send_control_char(cc[CcIndex::Vstop as usize])
            }
            TCION => {
                let cc = self.termios.read().cc;
                self.send_control_char(cc[CcIndex::Vstart as usize])
            }
            _ => Err(ErrorKind::InvalidInput),
        }
    }

    pub(crate) fn handle_tcsbrk(&self, duration: c_int) -> Result<(), ErrorKind> {
        if duration < 0 {
            return Err(ErrorKind::InvalidInput);
        }
        if duration == 0 {
            self.send_break_signal(duration)
        } else {
            self.wait_for_tx_empty()
        }
    }

    pub(crate) unsafe fn load_user_termios(ptr: *const Termios) -> Result<Termios, ErrorKind> {
        if ptr.is_null() {
            return Err(ErrorKind::InvalidInput);
        }
        Ok(*ptr)
    }

    pub(crate) unsafe fn store_user_termios(
        ptr: *mut Termios,
        termios: &Termios,
    ) -> Result<(), ErrorKind> {
        if ptr.is_null() {
            return Err(ErrorKind::InvalidInput);
        }
        *ptr = *termios;
        Ok(())
    }

    delegate! {
        to self.base {
            fn inc_open_count(&self) -> u32;
            fn dec_open_count(&self) -> u32;
            fn is_opened(&self) -> bool;
        }
    }

    fn rx_disable(&self) -> Result<(), SerialError> {
        let _ = atomic_wake(&self.rx_fifo.futex, 1);
        self.uart_ops.irqsave_lock().set_rx_interrupt(false);
        Ok(())
    }

    fn tx_disable(&self) -> Result<(), SerialError> {
        let _ = atomic_wake(&self.tx_fifo.futex, 1);
        self.uart_ops.irqsave_lock().set_tx_interrupt(false);
        // send all data in tx fifo
        self.xmitchars()?;
        Ok(())
    }

    fn fifo_rx(&self, buf: &mut [u8], is_nonblocking: bool) -> Result<usize, SerialError> {
        let len = buf.len();
        let mut count = 0;
        let mut reader = unsafe { self.rx_fifo.rb.reader() };

        loop {
            // read data from ringbuffer
            let slices = reader.pop_slices();
            let mut n = 0;
            for slice in slices {
                let slice_len = slice.len().min(len - count);
                buf[count..count + slice_len].copy_from_slice(&slice[..slice_len]);
                count += slice_len;
                n += slice_len;
            }
            reader.pop_done(n);

            if !is_nonblocking {
                // if the available data is less than the requested data, wait for data
                if n == 0 {
                    atomic_wait(&self.rx_fifo.futex, 0, None).map_err(|_| SerialError::TimedOut)?;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(count)
    }

    fn fifo_tx(&self, buf: &[u8], is_nonblocking: bool) -> Result<usize, SerialError> {
        let len = buf.len();
        let mut count = 0;
        let mut writer = unsafe { self.tx_fifo.rb.writer() };

        loop {
            // Get all slice for writing
            let slices = writer.push_slices();
            let mut n = 0;
            for slice in slices {
                if slice.is_empty() {
                    continue;
                }
                let slice_len = slice.len().min(len - count);
                slice[..slice_len].copy_from_slice(&buf[count..count + slice_len]);
                count += slice_len;
                n += slice_len;
            }
            if n > 0 {
                writer.push_done(n);
                self.uart_ops.irqsave_lock().set_tx_interrupt(true);
                // write some data to uart to trigger interrupt
                if !irq::is_in_irq() {
                    let _ = self.xmitchars();
                }
            }

            if !is_nonblocking && !irq::is_in_irq() {
                if !writer.is_empty() {
                    // wait for data to be written
                    atomic_wait(&self.tx_fifo.futex, 0, None).map_err(|_| SerialError::TimedOut)?;
                    self.uart_ops.irqsave_lock().set_tx_interrupt(false);
                } else if count >= len {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(count)
    }

    /// this Function is called from the UART interrupt handler
    /// when an interrupt is received indicating that there is more space in the
    /// transmit FIFO
    pub fn xmitchars(&self) -> Result<usize, SerialError> {
        let mut nbytes: usize = 0;
        {
            let mut uart_ops = self.uart_ops.irqsave_lock();
            // Safety: tx_fifo reader is only accessed in the UART interrupt handler
            let mut reader = unsafe { self.tx_fifo.rb.reader() };
            while !reader.is_empty() && uart_ops.write_ready()? {
                let buf = reader.pop_slice();
                match uart_ops.write(buf) {
                    Ok(sent) => {
                        nbytes += sent;
                        reader.pop_done(sent);
                    }
                    Err(e) => return Err(e),
                }
            }
            if reader.is_empty() {
                uart_ops.set_tx_interrupt(false);
            }
        }

        if nbytes > 0 {
            // TODO: add notify for poll/select
            let _ = atomic_wake(&self.tx_fifo.futex, 1);
        }

        Ok(nbytes)
    }

    /// this Function is called from the UART interrupt handler
    /// when an interrupt is received indicating that there is more data in the
    /// receive FIFO
    pub fn recvchars(&self) -> Result<usize, SerialError> {
        let mut nbytes: usize = 0;
        {
            let mut uart_ops = self.uart_ops.irqsave_lock();
            // Safety: rx_fifo writer is only accessed in the UART interrupt handler
            let mut writer = unsafe { self.rx_fifo.rb.writer() };
            while !writer.is_full() && uart_ops.read_ready()? {
                let buf = writer.push_slice();
                match uart_ops.read(buf) {
                    Ok(n) => {
                        nbytes += n;
                        writer.push_done(n);
                    }
                    Err(e) => return Err(e),
                }
            }
        }

        // TODO: add notify for poll/select
        if nbytes > 0 {
            let _ = atomic_wake(&self.rx_fifo.futex, 1);
        }

        Ok(nbytes)
    }
}

impl Device for Serial {
    fn name(&self) -> String {
        format!("ttyS{}", self.index)
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(4, 64 + self.index as usize)
    }

    fn open(&self) -> Result<(), ErrorKind> {
        if !self.is_opened() {
            let termios = self.termios_snapshot();
            let mut uart_ops = self.uart_ops.irqsave_lock();
            uart_ops.setup(&termios)?;
            uart_ops.set_rx_interrupt(true);
        }

        // Update device state
        self.inc_open_count();
        Ok(())
    }

    fn close(&self) -> Result<(), ErrorKind> {
        if !self.is_opened() {
            return Err(ErrorKind::NotFound);
        }

        if self.dec_open_count() == 0 {
            self.rx_disable()?;
            self.tx_disable()?;

            let mut uart_ops = self.uart_ops.irqsave_lock();
            uart_ops.ioctl(DeviceRequest::Close as u32, 0)?;
        }

        Ok(())
    }

    fn read(&self, _pos: u64, buf: &mut [u8], is_nonblocking: bool) -> Result<usize, ErrorKind> {
        self.fifo_rx(buf, is_nonblocking).map_err(ErrorKind::from)
    }

    fn write(&self, _pos: u64, buf: &[u8], is_nonblocking: bool) -> Result<usize, ErrorKind> {
        self.fifo_tx(buf, is_nonblocking).map_err(ErrorKind::from)
    }

    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        let mut uart_ops = self.uart_ops.irqsave_lock();
        uart_ops.ioctl(request, arg).map_err(ErrorKind::from)
    }
}
