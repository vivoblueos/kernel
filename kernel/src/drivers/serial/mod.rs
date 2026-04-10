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
    pub fn send_char(&self, c: u8) -> Result<(), Error> {
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
                let tx_next = self.tx_head.get() % CONFIG_SERIAL_TX_FIFO_SIZE;
                if (tx_next != self.tx_end.get()) {
                    self.tx_buffer.borrow_mut()[tx_next as usize] = c;
                    self.tx_head.set(tx_next);
                    self.dev.enable_interrupt(InterruptType::Tx);
                    return Ok(());
                } else {
                    self.dev.enable_interrupt(InterruptType::Tx);
                    return Err(code::EAGAIN);
                }
            }
        }
    }

    pub fn xmitchars() {
        while (SERIAL.tx_head.get() != SERIAL.tx_end.get()) && !SERIAL.dev.is_tx_fifo_full() {
            SERIAL
                .dev
                .write_data8(SERIAL.tx_buffer.borrow()[SERIAL.tx_end.get() as usize]);
            SERIAL
                .tx_end
                .set((SERIAL.tx_end.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE);
        }

        if SERIAL.tx_head.get() == SERIAL.tx_end.get() {
            SERIAL.dev.disable_interrupt(InterruptType::Tx);
        }
    }

    pub fn recvchars() {}
}
