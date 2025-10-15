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

use super::config::{APBP_CLOCK, GPIO_BASE, PL011_UART0_BASE, PL011_UART0_IRQNUM};
use crate::{
    arch::{irq, irq::IrqHandler},
    devices::{
        tty::{
            serial::{arm_pl011::Driver, Serial, UartOps},
            termios::{Cflags, Iflags, Lflags, Oflags, Termios},
        },
        DeviceManager,
    },
    irq::IrqTrace,
    sync::SpinLock,
};
use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
};
use core::{marker::PhantomData, ops};
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use spin::Once;

static UART0: Once<SpinLock<Driver<'static>>> = Once::new();
pub fn get_early_uart() -> &'static SpinLock<dyn UartOps> {
    UART0.call_once(|| {
        let mut uart = unsafe { Driver::new(PL011_UART0_BASE, APBP_CLOCK, PL011_UART0_IRQNUM) };
        let termios = Termios::new(
            Iflags::default(),
            Oflags::default(),
            Cflags::default(),
            Lflags::default(),
            115200,
            115200,
        );
        uart.enable(&termios);
        SpinLock::new(uart)
    })
}

static SERIAL0: Once<Arc<Serial>> = Once::new();

pub fn get_serial0() -> &'static Arc<Serial> {
    SERIAL0.call_once(|| {
        let mut uart = unsafe { Driver::new(PL011_UART0_BASE, APBP_CLOCK, PL011_UART0_IRQNUM) };
        let termios = Termios::new(
            Iflags::default(),
            Oflags::default(),
            Cflags::default(),
            Lflags::default(),
            115200,
            115200,
        );
        uart.enable(&termios);
        Arc::new(Serial::new(0, termios, Arc::new(SpinLock::new(uart))))
    })
}

pub struct Serial0Irq {}
impl IrqHandler for Serial0Irq {
    fn handle(&mut self) {
        let _ = IrqTrace::new(PL011_UART0_IRQNUM);
        let serial0 = get_serial0();
        let _ = serial0.recvchars();
        serial0.uart_ops.lock().clear_rx_interrupt();

        let _ = serial0.xmitchars();
        serial0.uart_ops.lock().clear_tx_interrupt();
    }
}

pub fn uart_init() -> Result<(), ErrorKind> {
    let serial0 = get_serial0();
    irq::set_trigger(PL011_UART0_IRQNUM, 0, irq::IrqTrigger::Level);
    let _ = irq::register_handler(PL011_UART0_IRQNUM, Box::new(Serial0Irq {}));
    DeviceManager::get().register_device(String::from("ttyS0"), serial0.clone())
}

// preserved cpu_id for multiple cores
pub fn enable_uart(cpu_id: usize) {
    irq::enable_irq_with_priority(PL011_UART0_IRQNUM, cpu_id, irq::Priority::Normal);
}
