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

// SPDX-License-Identifier: MIT OR Apache-2.0

use super::config;
use crate::{
    arch::{
        irq,
        irq::{IrqHandler, IrqNumber},
    },
    devices::{
        tty::{
            serial::{Serial, UartOps},
            termios::{Cflags, Iflags, Lflags, Oflags, Termios},
        },
        DeviceManager,
    },
    drivers::uart::arm_pl011::Driver,
    irq::IrqTrace,
    sync::SpinLock,
};
use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
};
use core::ptr::NonNull;
use embedded_io::{ErrorKind, ErrorType, Read, ReadReady, Write, WriteReady};
use safe_mmio::UniqueMmioPointer;
use spin::Once;

static UART0: Once<Arc<SpinLock<Driver<'static>>>> = Once::new();
// could add more UART if needed
pub fn get_early_uart(index: u32) -> Arc<SpinLock<dyn UartOps>> {
    match index {
        0 => UART0
            .get()
            .expect("uart_init must be called before get_early_uart")
            .clone(),
        _ => panic!("unsupported UART number"),
    }
}

static SERIAL0: Once<Arc<Serial>> = Once::new();
// could add more SERIAL if needed
pub fn get_serial(index: u32) -> &'static Arc<Serial> {
    match index {
        0 => SERIAL0
            .get()
            .expect("uart_init must be called before get_serial"),
        _ => panic!("unsupported SERIAL number"),
    }
}

pub fn uart_init(
    index: u32,
    base: u64,
    clock: u32,
    irq_num: IrqNumber,
    name: String,
) -> Result<(), ErrorKind> {
    match index {
        0 => {
            for cpu_id in 0..blueos_kconfig::NUM_CORES {
                irq::set_trigger(config::PL011_UART0_IRQNUM, cpu_id, irq::IrqTrigger::Level);
            }
            let _ = irq::register_handler(config::PL011_UART0_IRQNUM, Box::new(Serial0Irq {}));

            UART0.call_once(|| {
                let mut uart = unsafe { Driver::new(base, clock, irq_num) };
                let termios = Termios::new(
                    Iflags::default(),
                    Oflags::default(),
                    Cflags::default(),
                    Lflags::default(),
                    19200,
                    19200,
                );
                uart.enable(&termios);
                Arc::new(SpinLock::new(uart))
            });

            SERIAL0.call_once(|| {
                let termios = Termios::new(
                    Iflags::default(),
                    Oflags::default(),
                    Cflags::default(),
                    Lflags::default(),
                    19200,
                    19200,
                );
                Arc::new(Serial::new(index, termios, UART0.get().unwrap().clone()))
            });

            let serial = get_serial(0);
            DeviceManager::get().register_device(name, serial.clone())
        }
        _ => panic!("unsupported index for UART & SERIAL number"),
    }
}

pub fn enable_uart(cpu_id: usize, irq_num: IrqNumber) {
    irq::enable_irq_with_priority(irq_num, cpu_id, irq::Priority::Normal);
}

pub struct Serial0Irq {}
impl IrqHandler for Serial0Irq {
    fn handle(&mut self) {
        let _ = IrqTrace::new(config::PL011_UART0_IRQNUM);
        let serial0 = get_serial(0);
        let _ = serial0.recvchars();
        serial0.uart_ops.lock().clear_rx_interrupt();

        let _ = serial0.xmitchars();
        serial0.uart_ops.lock().clear_tx_interrupt();
    }
}
