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

use crate::{
    arch,
    arch::irq::IrqNumber,
    devices::tty::{
        serial::{Serial, SerialError, UartOps},
        termios::Termios,
    },
    sync::SpinLock,
    vfs::AccessMode,
};
use alloc::sync::Arc;
use bitflags::bitflags;
use core::{mem::MaybeUninit, ptr::NonNull};
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use safe_mmio::{
    field, field_shared,
    fields::{ReadPure, ReadPureWrite, ReadWrite, WriteOnly},
    UniqueMmioPointer,
};
use spin::{Mutex, Once};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct RecieverHoldingRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct TransmitterHoldingRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct InterruptEnableRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct FIFOControlRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct InterruptStatusRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct LineControlRegister(u8);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct LineStatusRegister(u8); //pub , can't leak private type

bitflags! {
    impl InterruptEnableRegister: u8 {
        const RX_ENABLE = 1 << 0;
        const TX_ENABLE = 1 << 1;
    }

    impl FIFOControlRegister: u8 {
        const FIFO_ENABLE = 1 << 0;
        const FIFO_CLEAR = 3 << 1;
    }

    impl LineControlRegister: u8 {
        const EIGHT_BITS = 3;
        const BAUD_LATCH = 1 << 7;
    }

    impl LineStatusRegister: u8 {
        const RX_READY = 1 << 0;
        const TX_IDLE = 1 << 5;
    }
}

/// RISCV unknown register map
#[derive(Clone, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
#[repr(C, align(4))]
pub struct UartRegisters {
    rhr_thr: ReadWrite<u8>, // u8 for compatibility
    ier: ReadWrite<InterruptEnableRegister>,
    fcr_isr: ReadWrite<FIFOControlRegister>, // share, but read-only for ISR, so can be labeled as FCR
    lcr: ReadWrite<LineControlRegister>,
    lsr: ReadWrite<LineStatusRegister>,
}

static UART_MUTEX: SpinLock<()> = SpinLock::new(());

pub(crate) struct Uart<'a> {
    regs: Mutex<UniqueMmioPointer<'a, UartRegisters>>,
}

unsafe impl core::marker::Sync for Uart<'_> {} // Mutex added on UniqueMmioPointer, still care do not get raw pointer from UniqueMmioPointer

impl<'a> Uart<'a> {
    /// Creates new UART instance.
    pub fn new(regs: UniqueMmioPointer<'a, UartRegisters>) -> Self {
        Self {
            regs: Mutex::new(regs),
        }
    }

    // pub(crate) fn init(&mut self, irq_num: IrqNumber) {
    pub(crate) fn init(&mut self) {
        let mut guard = self.regs.lock();
        // Disable interrupts.
        field!(guard, ier).write(InterruptEnableRegister(0));
        // Special mode to set baud rate.
        field!(guard, lcr).write(LineControlRegister::BAUD_LATCH);
        // LSB for baud rate of 38.4K.
        field!(guard, rhr_thr).write(0x03);
        // MSB for baud rate of 38.4K.
        field!(guard, ier).write(InterruptEnableRegister(0));
        // Leave set-baud mode, and set word length to 8 bits, no parity.
        field!(guard, lcr).write(LineControlRegister::EIGHT_BITS);
        // Reset and enable FIFOs.
        field!(guard, fcr_isr)
            .write(FIFOControlRegister::FIFO_ENABLE | FIFOControlRegister::FIFO_CLEAR);
        // Enable transmit and receive interrupts.
        field!(guard, ier)
            .write(InterruptEnableRegister::TX_ENABLE | InterruptEnableRegister::RX_ENABLE);
    }

    #[inline]
    pub fn write_bytes(&mut self, s: &str) -> usize {
        let l = UART_MUTEX.irqsave_lock();
        for c in s.bytes() {
            self.write_byte(c);
        }
        s.len()
    }
}

impl WriteReady for Uart<'_> {
    fn write_ready(&mut self) -> Result<bool, SerialError> {
        let mut guard = self.regs.lock();
        Ok(field!(guard, lsr)
            .read()
            .contains(LineStatusRegister::TX_IDLE))
    }
}

impl ReadReady for Uart<'_> {
    fn read_ready(&mut self) -> Result<bool, SerialError> {
        let mut guard = self.regs.lock();
        Ok(field!(guard, lsr)
            .read()
            .contains(LineStatusRegister::RX_READY))
    }
}

// This can be shared among all UartOps impl.
impl Read for Uart<'_> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, SerialError> {
        let _ = UART_MUTEX.irqsave_lock();
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

impl Write for Uart<'_> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, SerialError> {
        let _ = UART_MUTEX.irqsave_lock();
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
        let _ = UART_MUTEX.irqsave_lock();
        let mut guard = self.regs.lock();
        field!(guard, fcr_isr).write(FIFOControlRegister::FIFO_CLEAR);
        Ok(())
    }
}

impl ErrorType for Uart<'_> {
    type Error = SerialError;
}

impl UartOps for Uart<'_> {
    fn setup(&mut self, _: &Termios) -> Result<(), SerialError> {
        Ok(())
    }
    fn shutdown(&mut self) -> Result<(), SerialError> {
        Ok(())
    }
    #[inline]
    fn read_byte(&mut self) -> Result<u8, SerialError> {
        let mut guard = self.regs.lock();
        while !field!(guard, lsr)
            .read()
            .contains(LineStatusRegister::RX_READY)
        {}
        Ok(field!(guard, rhr_thr).read())
    }
    #[inline]
    fn write_byte(&mut self, c: u8) -> Result<(), SerialError> {
        let mut guard = self.regs.lock();
        while !field!(guard, lsr)
            .read()
            .contains(LineStatusRegister::TX_IDLE)
        {}
        field!(guard, rhr_thr).write(c);
        Ok(())
    }
    fn write_str(&mut self, s: &str) -> Result<(), SerialError> {
        self.write_bytes(s);
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

#[cfg(test)]
mod tests {
    use super::*;
    // use super::super::*;

    use crate::drivers::ic::plic::Plic;
    use blueos_test_macro::test; //need this macro for custom test framework instead of std default
    const PLIC_BASE: usize = 0x0c00_0000;
    const UART0_BASE: u32 = 0x1000_0000;
    const UART0_IRQ: IrqNumber = IrqNumber::new(10);

    static UART0: Once<Arc<SpinLock<Uart>>> = Once::new();
    static SERIAL0: Once<Arc<Serial>> = Once::new();

    static PLIC: Plic = Plic::new(PLIC_BASE);

    fn uart_init(index: u32) {
        match index {
            0 => {
                // Enable UART0 in PLIC.
                PLIC.enable(
                    arch::current_cpu_id(),
                    u32::try_from(usize::from(UART0_IRQ))
                        .expect("usize(64 bits) converts to u32 failed"),
                );
                // Set UART0 priority in PLIC.
                PLIC.set_priority(
                    u32::try_from(usize::from(UART0_IRQ))
                        .expect("usize(64 bits) converts to u32 failed"),
                    1,
                );

                UART0.call_once(|| {
                    Arc::new(SpinLock::new(Uart::new(unsafe {
                        UniqueMmioPointer::new(NonNull::new(UART0_BASE as *mut _).unwrap())
                    }))) // according to base, not always uart0
                });

                SERIAL0.call_once(|| {
                    Arc::new(Serial::new(
                        index,
                        Termios::default(),
                        UART0.get().unwrap().clone(),
                    ))
                });

                UART0.get().unwrap().lock().init();
            }
            _ => panic!("unsupported index for UART & SERIAL number"),
        }
    }

    #[test]
    fn test_uart_init() {
        uart_init(0);
        let mut temp_uart = Uart::new(unsafe {
            UniqueMmioPointer::new(NonNull::new(UART0_BASE as *mut _).unwrap())
        });
        let mut guard = temp_uart.regs.lock();
        let read_lcr = field!(guard, lcr).read();
        assert!(read_lcr.contains(LineControlRegister::EIGHT_BITS))
    }
}
