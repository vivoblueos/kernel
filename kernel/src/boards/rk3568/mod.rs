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

mod config;
use crate::{arch, arch::irq, error::Error, sync::SpinLock, time};
use blueos_driver::uart::ns16x50::Ns16x50Isr;
use blueos_kconfig::CONFIG_NUM_CORES;
pub(crate) use config::{MMU_L1_DEVICE_BASES, MMU_L1_NORMAL_BASES};
pub use config::{PHYS_DRAM_BASE, PHYS_DRAM_SIZE};
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
    irq::enable_irq_with_priority(
        config::CONSOLE_UART_IRQNUM,
        arch::current_cpu_id(),
        irq::Priority::Normal,
    );
    irq::enable_irq_with_priority(
        config::GENERIC_TIMER_IRQNUM,
        arch::current_cpu_id(),
        irq::Priority::Normal,
    );
    // RK3568 UART interrupts are level-triggered (active high) on the GIC.
    irq::set_trigger(
        config::CONSOLE_UART_IRQNUM,
        arch::current_cpu_id(),
        irq::IrqTrigger::Level,
    );
    let _ = arch::irq::register_handler(
        config::CONSOLE_UART_IRQNUM,
        Box::new(
            Ns16x50Isr::<{ config::CONSOLE_UART_BASE as usize }, _>::new(
                &crate::drivers::serial::TTY_SERIAL,
                Some(crate::drivers::serial::Serial::xmitchars),
                Some(crate::drivers::serial::Serial::recvchars),
            ),
        ),
    );
    let _ = arch::irq::register_handler(config::GENERIC_TIMER_IRQNUM, Box::new(TimerIrq {}));
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::ns16x50::Ns16x50,
     blueos_driver::uart::ns16x50::Ns16x50::new(
        config::CONSOLE_UART_BASE as usize,
     )),
}

crate::define_pin_states!(None);

pub struct TimerIrq;
impl IsrDesc for TimerIrq {
    fn service_isr(&self) {
        crate::time::handle_clock_interrupt();
    }
}
