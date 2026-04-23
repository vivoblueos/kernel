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

use core::{
    cell::{Cell, RefCell},
    sync::atomic::AtomicUsize,
};

use crate::{
    error::{code, Error},
    irq::is_in_irq,
    support::DisableInterruptGuard,
    sync::{atomic_wait::atomic_wait, atomic_wake, Semaphore, SpinLock},
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
    tx_futex: AtomicUsize,
    rx_buffer: [u8; CONFIG_SERIAL_RX_FIFO_SIZE as usize],
    rx_head: u32,
    rx_end: u32,
    critical_section_guard: SpinLock<()>,
}

/// Safety:
unsafe impl Sync for Serial {}

pub(crate) static SERIAL: Serial = Serial {
    dev: crate::boards::get_device!(console_uart),
    tx_buffer: RefCell::new([0; CONFIG_SERIAL_TX_FIFO_SIZE as usize]),
    tx_end: Cell::new(0),
    tx_head: Cell::new(0),
    tx_lock: RwLock::new(()),
    tx_futex: AtomicUsize::new(0),
    rx_buffer: [0; CONFIG_SERIAL_RX_FIFO_SIZE as usize],
    rx_head: 0,
    rx_end: 0,
    critical_section_guard: SpinLock::new(()),
};

impl Serial {
    pub fn send_bytes(bytes: &[u8], blocking: bool) -> Result<usize, Error> {
        if is_in_irq() {
            // same behavior as kearly_printkln!
            let _lock = SERIAL.critical_section_guard.irqsave_lock();
            for &b in bytes {
                SERIAL.send_byte_polling(b);
            }
            Ok(bytes.len())
        } else {
            let mut nbytes = 0;
            let _spinlock = SERIAL.tx_lock.write();
            SERIAL.dev.disable_interrupt(InterruptType::Tx);
            'e: for &b in bytes {
                match SERIAL.send_byte_fifo(b) {
                    Ok(()) => {
                        nbytes += 1;
                    }
                    Err(e) => match e.to_errno() {
                        e if e == code::EAGAIN.to_errno() && blocking => {
                            'i: loop {
                                // If the FIFO is full and we're in blocking mode, we need to
                                // trigger the TX interrupt to start sending out the data in FIFO.
                                SERIAL.trigger_tx_interrupt();
                                // Then we wait for the TX buffer to have space. In a real implementation,
                                // we would likely want to wait on a semaphore that gets signaled in the
                                // TX interrupt handler when space is available.
                                atomic_wait(&SERIAL.tx_futex, 0, crate::time::Tick::MAX);
                                match SERIAL.send_byte_fifo(b) {
                                    Ok(()) => break 'i,
                                    Err(e) => match e.to_errno() {
                                        e if e == code::EAGAIN.to_errno() => continue 'i,
                                        _ => break 'e,
                                    },
                                }
                            }
                            nbytes += 1;
                        }
                        _ => {
                            // For any other error, we just stop sending
                            // and return the number of bytes sent so far.
                            break;
                        }
                    },
                }
            }
            SERIAL.trigger_tx_interrupt();
            Ok(nbytes)
        }
    }

    #[inline(always)]
    fn send_byte_polling(&self, c: u8) {
        while self.dev.is_tx_fifo_full() {}
        self.dev.write_data8(c);
    }

    #[inline(always)]
    fn send_byte_fifo(&self, c: u8) -> Result<(), Error> {
        let tx_next = (self.tx_head.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE;
        if tx_next != self.tx_end.get() {
            self.tx_buffer.borrow_mut()[self.tx_head.get() as usize] = c;
            self.tx_head.set(tx_next);
            Ok(())
        } else {
            return Err(code::EAGAIN);
        }
    }

    #[inline(always)]
    fn trigger_tx_interrupt(&self) {
        let _lock = self.critical_section_guard.irqsave_lock();
        self.dev.enable_interrupt(InterruptType::Tx);
        // FIXME: In the certain SoCs that TX is an edge interrupt. It only fires
        // on a state change of TX buffer from full to empty. So, we need to
        // trigger the interrupt manually here to get interrupt processing going,
        // as there is no previous. But it's not common in MCU where TX is usually
        // a level interrupt, active for as long as TX buffer is empty. So we should
        // consider to make this behavior configurable in the future.
        Self::xmitchars();
    }

    pub fn xmitchars() {
        use blueos_hal::HasInterruptReg;

        #[cfg(smp)]
        static CRITICAL_SECTION: SpinLock<()> = SpinLock::new(());
        #[cfg(smp)]
        let _lock = CRITICAL_SECTION.irqsave_lock();

        let sent = if (SERIAL.tx_head.get() != SERIAL.tx_end.get()) && !SERIAL.dev.is_tx_fifo_full()
        {
            SERIAL
                .dev
                .write_data8(SERIAL.tx_buffer.borrow()[SERIAL.tx_end.get() as usize]);
            SERIAL
                .tx_end
                .set((SERIAL.tx_end.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE);
            true
        } else {
            false
        };

        if SERIAL.tx_head.get() == SERIAL.tx_end.get() {
            SERIAL.dev.disable_interrupt(InterruptType::Tx);
        }

        if sent {
            atomic_wake(&SERIAL.tx_futex, 1);
        }
    }

    pub fn recvchars() {}
}
