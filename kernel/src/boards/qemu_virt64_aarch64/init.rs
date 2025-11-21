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

use super::config;
use crate::{
    arch,
    arch::{
        irq,
        irq::{IrqHandler, IrqTrigger, Priority},
        registers::cntfrq_el0::CNTFRQ_EL0,
    },
    error::Error,
    scheduler,
    support::SmpStagedInit,
    time,
};
use alloc::boxed::Box;
use blueos_hal::HasInterruptReg;
use blueos_kconfig::NUM_CORES;
use core::sync::atomic::Ordering;
use tock_registers::interfaces::Readable;
static STAGING: SmpStagedInit = SmpStagedInit::new();

pub(crate) fn init() {
    STAGING.run(0, true, crate::boot::init_runtime);
    STAGING.run(1, true, crate::boot::init_heap);
    STAGING.run(2, false, arch::vector::init);
    STAGING.run(3, true, || unsafe {
        arch::irq::init(config::GICD as u64, config::GICR as u64, NUM_CORES, false)
    });
    STAGING.run(4, false, arch::irq::cpu_init);
    STAGING.run(5, false, || {
        let sys_clk = (CNTFRQ_EL0.get() * 1000) as u32;
        time::systick_init(sys_clk);
    });
    STAGING.run(6, false, || {
        irq::enable_irq_with_priority(
            config::PL011_UART0_IRQNUM,
            arch::current_cpu_id(),
            irq::Priority::Normal,
        );
    });
    STAGING.run(7, true, || arch::secondary_cpu_setup(config::PSCI_BASE));
    if arch::current_cpu_id() != 0 {
        scheduler::wait_and_then_start_schedule();
        unreachable!("Secondary cores should have jumped to the scheduler");
    }

    irq::set_trigger(
        config::PL011_UART0_IRQNUM,
        arch::current_cpu_id(),
        irq::IrqTrigger::Level,
    );
    let _ = irq::register_handler(config::PL011_UART0_IRQNUM, Box::new(Serial0Irq {}));
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::arm_pl011::ArmPl011<'static>,
     blueos_driver::uart::arm_pl011::ArmPl011::<'static>::new(
        config::PL011_UART0_BASE as _,
        config::APBP_CLOCK,
        None,
     )),
}

pub const DRAM_BASE: u64 = 0x4000_0000;

crate::define_pin_states!(None);

pub struct Serial0Irq {}
impl IrqHandler for Serial0Irq {
    fn handle(&mut self) {
        let uart = get_device!(console_uart);
        if let Some(handler) = unsafe {
            let intr_handler_cell = &*uart.intr_handler.get();
            intr_handler_cell.as_ref()
        } {
            handler();
        }
        uart.clear_interrupt(blueos_driver::uart::InterruptType::All);
    }
}
