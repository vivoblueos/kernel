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

use super::{config, PLIC};
use crate::{
    arch,
    arch::irq::IrqNumber,
    devices::tty::{
        serial::{Serial, SerialError, UartOps},
        termios::Termios,
    },
    drivers::uart::ns16550a::Uart,
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

static UART0: Once<Arc<SpinLock<Uart>>> = Once::new();
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

pub(crate) fn uart_init(index: u32) {
    match index {
        0 => {
            // Enable UART0 in PLIC.
            PLIC.enable(
                arch::current_cpu_id(),
                u32::try_from(usize::from(config::UART0_IRQ))
                    .expect("usize(64 bits) converts to u32 failed"),
            );
            // Set UART0 priority in PLIC.
            PLIC.set_priority(
                u32::try_from(usize::from(config::UART0_IRQ))
                    .expect("usize(64 bits) converts to u32 failed"),
                1,
            );

            UART0.call_once(|| {
                Arc::new(SpinLock::new(Uart::new(unsafe {
                    UniqueMmioPointer::new(NonNull::new(config::UART0 as *mut _).unwrap())
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
