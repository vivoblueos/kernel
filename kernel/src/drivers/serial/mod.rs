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
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    devices::{tty::termios::CcIndex, Device},
    error::code,
    irq::is_in_irq,
    kearly_println,
    scheduler::{self, is_schedule_ready, yield_me},
    support::DisableInterruptGuard,
    sync::{atomic_wait, atomic_wake, SpinLock},
    time::{self, Tick},
};
use blueos_driver::uart::{InterruptType, UartConfig, UartCtrlStatus};
use blueos_infra::tinyrwlock::RwLock;
use blueos_kconfig::{CONFIG_SERIAL_RX_FIFO_SIZE, CONFIG_SERIAL_TX_FIFO_SIZE};
use embedded_io::ErrorKind;
use libc::{TCIFLUSH, TCIOFF, TCIOFLUSH, TCION, TCOFLUSH, TCOOFF, TCOON};

const DEFAULT_BREAK_DURATION_MS: usize = 250;
const DEFAULT_TX_DRAIN_TIMEOUT_MS: usize = 5000;

pub struct Serial {
    dev: &'static dyn blueos_hal::uart::Uart<UartConfig, (), InterruptType, UartCtrlStatus>,
    tx_buffer: RefCell<[u8; CONFIG_SERIAL_TX_FIFO_SIZE as usize]>,
    tx_end: Cell<u32>,
    tx_head: Cell<u32>,
    tx_lock: RwLock<()>,
    rx_buffer: RefCell<[u8; CONFIG_SERIAL_RX_FIFO_SIZE as usize]>,
    rx_head: Cell<u32>,
    rx_end: Cell<u32>,
    tx_futex: AtomicUsize,
    rx_futex: AtomicUsize,
    owner_cnts: Cell<i32>,
    critical_section_guard: SpinLock<()>,
}

/// Safety:
/// - Single-core: thread-side enqueue is serialized by `tx_lock`; TX IRQ is disabled around
///   enqueue/retry critical region to avoid producer-side interleaving with TX ISR.
///
/// - SMP: accesses to `tx_buffer/tx_head/tx_end` in TX producer/consumer paths are additionally
///   serialized by `critical_section_guard` so these shared fields are not concurrently mutated.
/// - Pending TX IRQ may still run once after a disable operation due to interrupt timing, but this
///   is treated as timing jitter (observable send time variation), not a duplicated-byte data race.
/// - Thread-side enqueue is serialized by `tx_lock`.
/// - TX-side dequeue only advances `tx_end` and runs with interrupt context rules.
/// - `send_bytes` disables TX interrupt around enqueue/retry critical region, so producer-side
///   updates to `tx_buffer/tx_head` are not interleaved by TX ISR.
unsafe impl Sync for Serial {}

pub static TTY_SERIAL: Serial = Serial {
    dev: crate::boards::get_device!(console_uart),
    tx_buffer: RefCell::new([0; CONFIG_SERIAL_TX_FIFO_SIZE as usize]),
    tx_end: Cell::new(0),
    tx_head: Cell::new(0),
    tx_lock: RwLock::new(()),
    rx_buffer: RefCell::new([0; CONFIG_SERIAL_RX_FIFO_SIZE as usize]),
    rx_head: Cell::new(0),
    rx_end: Cell::new(0),
    tx_futex: AtomicUsize::new(0),
    rx_futex: AtomicUsize::new(0),
    owner_cnts: Cell::new(0),
    critical_section_guard: SpinLock::new(()),
};

impl Serial {
    pub fn send_bytes(&self, bytes: &[u8], is_nonblocking: bool) -> Result<usize, ErrorKind> {
        if is_in_irq() {
            // Caution: logging in IRQ context can extend interrupt-off latency.
            //
            // We intentionally use polling here (same behavior as `kearly_printkln!`) instead
            // of waiting for TX IRQ progress:
            // 1) some IRQ contexts run with interrupts masked;
            // 2) current IRQ priority may be higher than UART TX IRQ, so TX handler cannot run.
            //
            // In those cases, relying on TX interrupt-driven drain may stall forever. Polling
            // guarantees forward progress for emergency logs, but callers should keep IRQ logs
            // short and infrequent.
            #[cfg(smp)]
            let _lock = self.critical_section_guard.irqsave_lock();
            for &b in bytes {
                self.send_byte_polling(b);
            }
            Ok(bytes.len())
        } else {
            let mut nbytes = 0;
            let _spinlock = self.tx_lock.write();
            self.dev.disable_interrupt(InterruptType::Tx);
            'e: for &b in bytes {
                #[cfg(smp)]
                let _lock = self.critical_section_guard.irqsave_lock();

                match self.send_byte_fifo(b) {
                    Ok(()) => {
                        nbytes += 1;
                    }
                    Err(ErrorKind::OutOfMemory) => {
                        if !is_nonblocking {
                            #[cfg(smp)]
                            drop(_lock);
                            'i: loop {
                                let tx_seq = self.tx_futex.load(Ordering::Acquire);
                                // If the FIFO is full and we're in blocking mode, we need to
                                // trigger the TX interrupt to start sending out the data in FIFO.
                                self.trigger_tx_interrupt();
                                if is_schedule_ready() {
                                    match atomic_wait(&self.tx_futex, tx_seq, Tick::MAX) {
                                        Ok(()) | Err(code::EAGAIN) => {}
                                        Err(code::ETIMEDOUT) => return Err(ErrorKind::TimedOut),
                                        Err(_) => return Err(ErrorKind::Other),
                                    }
                                } else {
                                    while (self.is_tx_full()) {}
                                }
                                self.dev.disable_interrupt(InterruptType::Tx);
                                #[cfg(smp)]
                                let _lock = self.critical_section_guard.irqsave_lock();
                                match self.send_byte_fifo(b) {
                                    Ok(()) => break 'i,
                                    Err(ErrorKind::OutOfMemory) => {
                                        continue 'i;
                                    }
                                    Err(_) => break 'e,
                                }
                            }
                            nbytes += 1;
                        }
                    }
                    Err(_) => {
                        // For any other error, we just stop sending
                        // and return the number of bytes sent so far.
                        break;
                    }
                }
            }
            self.trigger_tx_interrupt();
            Ok(nbytes)
        }
    }

    pub fn read_bytes(&self, bytes: &mut [u8], is_nonblocking: bool) -> Result<usize, ErrorKind> {
        let mut nbytes = 0;
        for byte in bytes {
            loop {
                if let Some(c) = self.get_char() {
                    *byte = c;
                    nbytes += 1;
                    break;
                }
                if is_nonblocking {
                    return Ok(nbytes);
                }

                if !is_schedule_ready() {
                    continue;
                }

                // `rx_futex` is used as a sequence counter. Waiting on a captured sequence
                // value avoids lost wakeups between empty-check and wait enqueue.
                let rx_seq = self.rx_futex.load(Ordering::Acquire);

                if let Some(c) = self.get_char() {
                    *byte = c;
                    nbytes += 1;
                    break;
                }

                match atomic_wait(&self.rx_futex, rx_seq, Tick::MAX) {
                    Ok(()) | Err(code::EAGAIN) => {}
                    Err(code::ETIMEDOUT) => return Err(ErrorKind::TimedOut),
                    Err(_) => return Err(ErrorKind::Other),
                }
            }
        }
        Ok(nbytes)
    }

    pub fn handle_tcflsh(&self, action: i32) -> Result<(), ErrorKind> {
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

    pub fn handle_tcxonc(&self, action: i32, cc: &[u8; 12]) -> Result<(), ErrorKind> {
        match action {
            TCOOFF => {
                self.dev.disable_interrupt(InterruptType::Tx);
                Ok(())
            }
            TCOON => {
                self.dev.enable_interrupt(InterruptType::Tx);
                self.trigger_tx_interrupt();
                Ok(())
            }
            TCIOFF => {
                self.send_control_char(cc[CcIndex::Vstop as usize])?;
                Ok(())
            }
            TCION => {
                self.send_control_char(cc[CcIndex::Vstart as usize])?;
                Ok(())
            }
            _ => Err(ErrorKind::InvalidInput),
        }
    }

    pub fn handle_tcsbrk(&self, duration: i32) -> Result<(), ErrorKind> {
        if duration < 0 {
            return Err(ErrorKind::InvalidInput);
        }
        if duration == 0 {
            // send break signal
            self.wait_for_tx_drain_complete()?;
            let lock = self.critical_section_guard.irqsave_lock();
            self.dev
                .set_break_signal(true)
                .map_err(|_| ErrorKind::Other)?;

            scheduler::suspend_me_for(
                time::Tick::from_millis(DEFAULT_BREAK_DURATION_MS as u64),
                Some(lock),
            );

            let _lock = self.critical_section_guard.irqsave_lock();
            self.dev
                .set_break_signal(false)
                .map_err(|_| ErrorKind::Other)
        } else {
            self.wait_for_tx_drain_complete()
        }
    }

    /// Wait until software TX ring becomes empty.
    ///
    /// This does not guarantee UART shift register/FIFO are fully drained.
    ///
    /// To avoid unbounded waits when TX progress is broken, this returns
    /// `ErrorKind::TimedOut` after a bounded timeout.
    pub fn wait_for_tx_empty(&self) -> Result<(), ErrorKind> {
        let start = Tick::now();
        let timeout = Tick::from_millis(DEFAULT_TX_DRAIN_TIMEOUT_MS as u64);
        loop {
            if self.is_tx_empty() {
                break;
            }
            if Tick::now().since(start) >= timeout {
                return Err(ErrorKind::TimedOut);
            }
            if is_schedule_ready() {
                yield_me();
            }
        }
        Ok(())
    }

    /// Wait until both software TX queue and hardware transmitter are drained.
    ///
    /// Use this for TCSETSW/TCSETSF/TCSBRK-like semantics.
    ///
    /// Returns `ErrorKind::TimedOut` if hardware never reaches idle state.
    pub fn wait_for_tx_drain_complete(&self) -> Result<(), ErrorKind> {
        self.wait_for_tx_empty()?;
        let start = Tick::now();
        let timeout = Tick::from_millis(DEFAULT_TX_DRAIN_TIMEOUT_MS as u64);
        loop {
            if !self.dev.is_bus_busy() {
                break;
            }
            if Tick::now().since(start) >= timeout {
                return Err(ErrorKind::TimedOut);
            }
            if is_schedule_ready() {
                yield_me();
            }
        }
        Ok(())
    }

    #[inline(always)]
    fn send_control_char(&self, ch: u8) -> Result<(), ErrorKind> {
        self.send_byte_polling(ch);
        Ok(())
    }

    #[inline(always)]
    fn flush_rx_fifo(&self) {
        let _lock = self.critical_section_guard.irqsave_lock();
        self.rx_head.set(0);
        self.rx_end.set(0);
        self.rx_futex.fetch_add(1, Ordering::Release);
        let _ = atomic_wake(&self.rx_futex, usize::MAX);
    }

    #[inline(always)]
    fn flush_tx_fifo(&self) {
        let _lock = self.critical_section_guard.irqsave_lock();
        self.tx_head.set(0);
        self.tx_end.set(0);
        self.tx_futex.fetch_add(1, Ordering::Release);
        let _ = atomic_wake(&self.tx_futex, usize::MAX);
    }

    #[inline(always)]
    fn send_byte_polling(&self, c: u8) {
        while self.dev.is_tx_fifo_full() {}
        self.dev.write_data8(c);
    }

    #[inline(always)]
    fn send_byte_fifo(&self, c: u8) -> Result<(), ErrorKind> {
        let tx_next = (self.tx_head.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE;
        if tx_next != self.tx_end.get() {
            self.tx_buffer.borrow_mut()[self.tx_head.get() as usize] = c;
            self.tx_head.set(tx_next);
            Ok(())
        } else {
            Err(ErrorKind::OutOfMemory)
        }
    }

    #[inline(always)]
    fn trigger_tx_interrupt(&self) {
        // FIXME: When the prority of TX interrupt is higher than current execution context,
        // we may trigger the interrupt before exiting critical section, which may cause the interrupt
        // handler to run before we finish updating the TX buffer state. But it's not a problem as the interrupt
        // handler will check the buffer state and return immediately if there's no data to send.
        // So we can just accept this minor timing jitter for simplicity.
        let _lock = self.critical_section_guard.irqsave_lock();
        self.dev.enable_interrupt(InterruptType::Tx);
        // FIXME: In the certain SoCs that TX is an edge interrupt. It only fires
        // on a state change of TX buffer from full to empty. So, we need to
        // trigger the interrupt manually here to get interrupt processing going,
        // as there is no previous. But it's not common in MCU where TX is usually
        // a level interrupt, active for as long as TX buffer is empty. So we should
        // consider to make this behavior configurable in the future.
        self.consumer_byte();
    }

    #[inline(always)]
    fn consumer_byte(&self) -> bool {
        if (self.tx_head.get() != self.tx_end.get() && !self.dev.is_tx_fifo_full()) {
            self.dev
                .write_data8(self.tx_buffer.borrow()[self.tx_end.get() as usize]);
            self.tx_end
                .set((self.tx_end.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE);
            self.tx_futex.fetch_add(1, Ordering::Release);
            let _ = atomic_wake(&self.tx_futex, 1);

            if self.tx_head.get() == self.tx_end.get() {
                self.dev.disable_interrupt(InterruptType::Tx);
            }

            true
        } else {
            false
        }
    }

    #[inline(always)]
    fn get_char(&self) -> Option<u8> {
        let _lock = self.critical_section_guard.irqsave_lock();
        if self.rx_head.get() != self.rx_end.get() {
            let c = self.rx_buffer.borrow()[self.rx_end.get() as usize];
            self.rx_end
                .set((self.rx_end.get() + 1) % CONFIG_SERIAL_RX_FIFO_SIZE);
            Some(c)
        } else {
            None
        }
    }

    #[inline(always)]
    fn is_tx_empty(&self) -> bool {
        #[cfg(smp)]
        {
            let _lock = self.critical_section_guard.irqsave_lock();
            self.tx_head.get() == self.tx_end.get()
        }

        #[cfg(not(smp))]
        {
            self.tx_head.get() == self.tx_end.get()
        }
    }

    #[inline(always)]
    fn is_tx_full(&self) -> bool {
        #[cfg(smp)]
        {
            let _lock = self.critical_section_guard.irqsave_lock();
            (self.tx_head.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE == self.tx_end.get()
        }

        #[cfg(not(smp))]
        {
            (self.tx_head.get() + 1) % CONFIG_SERIAL_TX_FIFO_SIZE == self.tx_end.get()
        }
    }

    /// only be used in irq handler
    pub(crate) fn xmitchars(&self) {
        use blueos_hal::HasInterruptReg;

        #[cfg(smp)]
        let _lock = self.critical_section_guard.irqsave_lock();

        self.consumer_byte();
    }

    /// only be used in irq handler
    pub(crate) fn recvchars(&self) {
        #[cfg(smp)]
        let _lock = self.critical_section_guard.irqsave_lock();

        let mut nbytes = 0;
        while (!self.dev.is_rx_fifo_empty()) {
            let nexthead = (self.rx_head.get() + 1) % CONFIG_SERIAL_RX_FIFO_SIZE;

            match self.dev.read_data8() {
                Ok(c) => {
                    // If the RX buffer is full, we just drop the incoming data.
                    // It's necessary to trigger next irq.
                    if (nexthead != self.rx_end.get()) {
                        self.rx_buffer.borrow_mut()[self.rx_head.get() as usize] = c;
                        self.rx_head.set(nexthead);
                    }
                }
                Err(e) => {
                    kearly_println!("Error reading from serial RX FIFO {:?}", e);
                }
            }
        }

        if (self.rx_head.get() >= self.rx_end.get()) {
            nbytes = (self.rx_head.get() - self.rx_end.get()) as usize;
        } else {
            nbytes = (CONFIG_SERIAL_RX_FIFO_SIZE - self.rx_end.get() + self.rx_head.get()) as usize;
        }

        if nbytes > 0 {
            self.rx_futex.fetch_add(1, Ordering::Release);
            let _ = atomic_wake(&self.rx_futex, 1);
        }
    }

    pub fn open(&self, config: UartConfig) -> Result<(), ErrorKind> {
        let _lock = self.critical_section_guard.irqsave_lock();
        self.dev
            .configure(&config)
            .map_err(|_| ErrorKind::InvalidData)?;
        self.dev.enable();
        self.dev.clear_interrupt(InterruptType::All);
        self.dev.enable_interrupt(InterruptType::Rx);
        self.owner_cnts.set(self.owner_cnts.get() + 1);

        Ok(())
    }

    pub fn reconfigure(&self, config: UartConfig) -> Result<(), ErrorKind> {
        let _lock = self.critical_section_guard.irqsave_lock();
        self.dev
            .configure(&config)
            .map_err(|_| ErrorKind::InvalidData)?;

        if self.owner_cnts.get() > 0 {
            self.dev.enable();
            self.dev.enable_interrupt(InterruptType::Rx);
            if self.tx_head.get() != self.tx_end.get() {
                self.dev.enable_interrupt(InterruptType::Tx);
            }
        }

        Ok(())
    }

    pub fn close(&self) -> Result<(), ErrorKind> {
        let _lock = self.critical_section_guard.irqsave_lock();
        let owners = self.owner_cnts.get();
        if owners <= 0 {
            return Ok(());
        }

        let remaining = owners - 1;
        self.owner_cnts.set(remaining);
        if remaining == 0 {
            self.dev.disable_interrupt(InterruptType::Rx);
            self.dev.disable_interrupt(InterruptType::Tx);
            self.dev.disable();
        }
        Ok(())
    }
}
