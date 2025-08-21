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
    arch::irq::IrqNumber,
    devices::{
        tty::{
            serial::{Serial, UartOps},
            termios::Termios,
        },
        Device, DeviceManager,
    },
    drivers::uart::cmsdk_uart::Driver,
    irq::IrqTrace,
    sync::SpinLock,
    vfs::AccessMode,
};
use alloc::{string::String, sync::Arc};
use embedded_io::ErrorKind;
use spin::Once;

static UART0: Once<Arc<SpinLock<Driver>>> = Once::new();
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
    base: u32,
    clock: u32,
    rx_irq_num: IrqNumber,
    tx_irq_num: IrqNumber,
    name: String,
) -> Result<(), ErrorKind> {
    // must be called before get_serial and get_early_uart

    match index {
        0 => {
            UART0.call_once(|| {
                let mut uart =
                    unsafe { Driver::new(base as *mut u32, clock, rx_irq_num, tx_irq_num) };
                uart.enable(115200);
                Arc::new(SpinLock::new(uart))
            });

            SERIAL0.call_once(|| {
                Arc::new(Serial::new(
                    index,
                    Termios::default(),
                    UART0.get().unwrap().clone(),
                ))
            });
        }
        _ => panic!("unsupported index for UART & SERIAL number"),
    }

    let serial = get_serial(0);
    DeviceManager::get().register_device(name, serial.clone())
}

#[no_mangle]
pub unsafe extern "C" fn uart0rx_handler() {
    let _ = IrqTrace::new(config::UART0RX_IRQn);
    let uart = get_serial(0);
    uart.uart_ops.irqsave_lock().clear_rx_interrupt();
    if let Err(_e) = uart.recvchars() {
        // println!("UART RX error: {:?}", e);
    }
}
#[no_mangle]
pub unsafe extern "C" fn uart0tx_handler() {
    let _ = IrqTrace::new(config::UART0TX_IRQn);
    let uart = get_serial(0);
    uart.uart_ops.irqsave_lock().clear_tx_interrupt();
    if let Err(_e) = uart.xmitchars() {
        // println!("UART TX error: {:?}", e);
    }
}
