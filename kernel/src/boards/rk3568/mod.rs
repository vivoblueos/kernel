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

mod config;
use crate::{arch, error::Error, sync::SpinLock, time};
use blueos_driver::uart::ns16x50::Ns16x50Isr;
use blueos_kconfig::CONFIG_NUM_CORES;
pub(crate) use config::{MMU_L1_DEVICE_BASES, MMU_L1_NORMAL_BASES};
use core::sync::atomic::Ordering;
pub type ClockImpl = crate::devices::clock::gic_generic_timer::GenericClock;
use alloc::boxed::Box;
use blueos_hal::isr::IsrDesc;

pub(crate) fn init() {
    crate::boot::init_runtime();
    crate::boot::init_heap();
    arch::vector::init();
    unsafe {
        arch::irq::init(
            config::GICD as u64,
            config::GICR as u64,
            CONFIG_NUM_CORES as usize,
            false,
        )
    };
    arch::irq::cpu_init();
    let _ = arch::irq::register_handler(
        config::PL011_UART0_IRQNUM,
        Box::new(Ns16x50Isr::<{ config::PL011_UART0_BASE as usize }, _>::new(
            &crate::drivers::serial::TTY_SERIAL,
            Some(crate::drivers::serial::Serial::xmitchars),
            Some(crate::drivers::serial::Serial::recvchars),
        )),
    );
    let _ = arch::irq::register_handler(config::GENERIC_TIMER_IRQNUM, Box::new(TimerIrq {}));
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::ns16x50::Ns16x50,
     blueos_driver::uart::ns16x50::Ns16x50::new(
        0xFE660000,
     )),
}

crate::define_pin_states!(None);

pub struct TimerIrq;
impl IsrDesc for TimerIrq {
    fn service_isr(&self) {
        crate::time::handle_clock_interrupt();
    }
}
