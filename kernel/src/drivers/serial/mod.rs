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

use core::cell::{Cell, RefCell};

use crate::{
    error::{code, Error},
    irq::is_in_irq,
    sync::{Semaphore, SpinLock},
};
use blueos_driver::uart::{InterruptType, UartConfig, UartCtrlStatus};
use blueos_infra::tinyrwlock::RwLock;
use blueos_kconfig::{CONFIG_SERIAL_RX_FIFO_SIZE, CONFIG_SERIAL_TX_FIFO_SIZE};

pub struct Serial {
    dev: &'static dyn blueos_hal::uart::Uart<UartConfig, (), InterruptType, UartCtrlStatus>,
    tx_buffer: RefCell<[u8; CONFIG_SERIAL_TX_FIFO_SIZE as usize]>,
    tx_end: Cell<u32>,
    tx_head: Cell<u32>,
    tx_lock: RwLock<()>,
    rx_buffer: [u8; CONFIG_SERIAL_RX_FIFO_SIZE as usize],
    rx_head: u32,
    rx_end: u32,
}

/// Safety:
unsafe impl Sync for Serial {}

pub(crate) static SERIAL: Serial = Serial {
    dev: crate::boards::get_device!(console_uart),
    tx_buffer: RefCell::new([0; CONFIG_SERIAL_TX_FIFO_SIZE as usize]),
    tx_end: Cell::new(0),
    tx_head: Cell::new(0),
    tx_lock: RwLock::new(()),
    rx_buffer: [0; CONFIG_SERIAL_RX_FIFO_SIZE as usize],
    rx_head: 0,
    rx_end: 0,
};

impl Serial {
    pub fn send_buffer(&self, buf: &[u8], block: bool) -> Result<usize, Error> {
        let mut sent = 0;
        for c in buf {
            match self.send_char(*c) {
                Ok(()) => sent += 1,
                Err(Error::EAGAIN) if block => {
                    // FIXME: If blocking, wait for space in TX FIFO
                }
                Err(e) => return Err(e),
            }
        }
        self.dev.enable_interrupt(InterruptType::Tx);
        Self::xmitchars();
        Ok(sent)
    }

    fn send_char(&self, c: u8) -> Result<(), Error> {
        if is_in_irq() || !crate::arch::local_irq_enabled() {
            // If local interrupt is disabled, we are in critical section, and we can't sleep.
            // So we just try to send the character directly, and if the tx fifo is full, we drop the character.
            // if !self.dev.is_tx_fifo_full() {
            //     self.dev.write_data8(c);
            //     return Ok(());
            // } else {
            //     return Err(code::EAGAIN);
            // }
            while self.dev.is_tx_fifo_full() {}
            self.dev.write_data8(c);
            Ok(())
        } else {
            loop {
                let _lock = self.tx_lock.write();
                self.dev.disable_interrupt(InterruptType::Tx);
                // Safety: tx_buffer cann't be accessed by other thread until the lock is released.
                let tx_next = (self.tx_head.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE;
                if (tx_next != self.tx_end.get()) {
                    self.tx_buffer.borrow_mut()[self.tx_head.get() as usize] = c;
                    self.tx_head.set(tx_next);

                    // Kick TX once in process context so TX flow can start even if
                    // enabling TX interrupt alone doesn't immediately raise an interrupt.
                    Self::xmitchars();
                    if self.tx_head.get() != self.tx_end.get() {
                        self.dev.enable_interrupt(InterruptType::Tx);
                    }
                    return Ok(());
                } else {
                    self.dev.enable_interrupt(InterruptType::Tx);
                    return Err(code::EAGAIN);
                }
            }
        }
    }

    /// # Safety
    /// `xmitchars` has no internal lock and relies on external serialization.
    ///
    /// The current valid call sites are:
    /// 1. TX IRQ handler path.
    /// 2. `send_char` path, where TX interrupt is disabled before queue updates.
    ///
    /// Under this single-core usage model, there is no real concurrent access
    /// to `tx_head`/`tx_end`/`tx_buffer`. Do not call this function from any
    /// other path unless synchronization rules are revisited.
    pub fn xmitchars() {
        use blueos_hal::HasInterruptReg;

        let mut nbytes = 0u16;

        while (SERIAL.tx_head.get() != SERIAL.tx_end.get()) && !SERIAL.dev.is_tx_fifo_full() {
            SERIAL
                .dev
                .write_data8(SERIAL.tx_buffer.borrow()[SERIAL.tx_end.get() as usize]);
            SERIAL
                .tx_end
                .set((SERIAL.tx_end.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE);
            nbytes += 1;
        }

        if SERIAL.tx_head.get() == SERIAL.tx_end.get() {
            SERIAL.dev.disable_interrupt(InterruptType::Tx);
        }

        if nbytes > 0 {
            // FIXME: We should notify some semaphore here to wake up
            // the thread waiting for tx buffer to be empty.
        }
    }

    pub fn recvchars() {}
}
