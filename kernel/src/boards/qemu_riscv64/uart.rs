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

// This code is based on https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/uart.c
// Copyright (c) 2024 - present Microsoft Corporation
// SPDX-License-Identifier: MIT

use super::PLIC;
use crate::{
    arch,
    devices::tty::{
        serial::{Serial, SerialError, UartOps},
        termios::Termios,
    },
    sync::SpinLock,
    vfs::AccessMode,
};
use alloc::sync::Arc;
use core::mem::MaybeUninit;
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use spin::Once;

const UART0: usize = 0x1000_0000;
const UART0_IRQ: usize = 10;
const RHR: usize = 0;
const THR: usize = 0;
const IER: usize = 1;
const IER_RX_ENABLE: u8 = 1;
const IER_TX_ENABLE: u8 = 1 << 1;
const FCR: usize = 2;
const FCR_FIFO_ENABLE: u8 = 1;
const FCR_FIFO_CLEAR: u8 = 3 << 1;
const ISR: usize = 2;
const LCR: usize = 3;
const LCR_EIGHT_BITS: u8 = 3;
const LCR_BAUD_LATCH: u8 = 1 << 7;
const LSR: usize = 5;
const LSR_RX_READY: u8 = 1;
const LSR_TX_IDLE: u8 = 1 << 5;

#[inline]
fn map_reg(reg: usize) -> *mut u8 {
    unsafe { (UART0 + reg) as *mut u8 }
}

#[inline]
fn write_reg(reg: usize, val: u8) {
    unsafe { map_reg(reg).write(val) }
}

#[inline]
fn read_reg(reg: usize) -> u8 {
    unsafe { map_reg(reg).read() }
}

#[inline]
pub fn write_byte(c: u8) -> usize {
    while read_reg(LSR) & LSR_TX_IDLE == 0 {}
    write_reg(THR, c);
    1
}

#[inline]
pub fn read_byte() -> u8 {
    while read_reg(LSR) & LSR_RX_READY == 0 {}
    read_reg(RHR)
}

#[inline]
pub fn write_bytes(s: &str) -> usize {
    let l = UART0_MUTEX.irqsave_lock();
    for c in s.bytes() {
        write_byte(c);
    }
    s.len()
}

static UART0_MUTEX: SpinLock<()> = SpinLock::new(());
static UART0_DEVICE: MaybeUninit<SpinLock<Uart>> = MaybeUninit::uninit();

pub(super) fn init() {
    // Disable interrupts.
    write_reg(IER, 0x00);
    // Special mode to set baud rate.
    write_reg(LCR, LCR_BAUD_LATCH);
    // LSB for baud rate of 38.4K.
    write_reg(0, 0x03);
    // MSB for baud rate of 38.4K.
    write_reg(1, 0x00);
    // Leave set-baud mode, and set word length to 8 bits, no parity.
    write_reg(LCR, LCR_EIGHT_BITS);
    // Reset and enable FIFOs.
    write_reg(FCR, FCR_FIFO_ENABLE | FCR_FIFO_CLEAR);
    // Enable transmit and receive interrupts.
    write_reg(IER, IER_TX_ENABLE | IER_RX_ENABLE);
    // Enable UART0 in PLIC.
    PLIC.enable(arch::current_cpu_id(), UART0_IRQ as u32);
    // Set UART0 priority in PLIC.
    PLIC.set_priority(UART0_IRQ as u32, 1);
}

pub fn get_early_uart() -> &'static SpinLock<dyn UartOps> {
    unsafe { UART0_DEVICE.assume_init_ref() }
}

// TODO: This might be reused by other RISCV boards. Move to a common
// module.
struct Uart;

unsafe impl Send for Uart {}
unsafe impl Sync for Uart {}

impl WriteReady for Uart {
    fn write_ready(&mut self) -> Result<bool, SerialError> {
        Ok((read_reg(LSR) & LSR_TX_IDLE) != 0)
    }
}

impl ReadReady for Uart {
    fn read_ready(&mut self) -> Result<bool, SerialError> {
        Ok((read_reg(LSR) & LSR_RX_READY) != 0)
    }
}

// This can be shared among all UartOps impl.
impl Read for Uart {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, SerialError> {
        let _guard = UART0_MUTEX.irqsave_lock();
        while !self.read_ready()? {
            core::hint::spin_loop();
        }

        let mut r = 0;
        while r < buf.len() {
            let c = self.read_byte()?;
            buf[r] = c;
            r += 1;
        }
        Ok(r)
    }
}

impl Write for Uart {
    fn write(&mut self, buf: &[u8]) -> Result<usize, SerialError> {
        let _guard = UART0_MUTEX.irqsave_lock();
        while !self.write_ready()? {
            core::hint::spin_loop();
        }
        let mut w = 0;
        while w < buf.len() {
            self.write_byte(buf[w])?;
            w += 1;
        }
        Ok(w)
    }

    fn flush(&mut self) -> Result<(), SerialError> {
        let _guard = UART0_MUTEX.irqsave_lock();
        write_reg(FCR, FCR_FIFO_CLEAR);
        Ok(())
    }
}

impl ErrorType for Uart {
    type Error = SerialError;
}

impl UartOps for Uart {
    fn setup(&mut self, _: &Termios) -> Result<(), SerialError> {
        Ok(())
    }
    fn shutdown(&mut self) -> Result<(), SerialError> {
        Ok(())
    }
    fn read_byte(&mut self) -> Result<u8, SerialError> {
        Ok(read_byte())
    }
    fn write_byte(&mut self, c: u8) -> Result<(), SerialError> {
        write_byte(c);
        Ok(())
    }
    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        write_bytes(s);
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

static SERIAL0: Once<Arc<Serial>> = Once::new();

pub fn get_serial0() -> &'static Arc<Serial> {
    SERIAL0.call_once(|| {
        let uart = Arc::new(SpinLock::new(Uart));
        Arc::new(Serial::new(0, Termios::default(), uart))
    })
}
