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
use crate::{arch, arch::irq, scheduler, support::SmpStagedInit};
use blueos_driver::uart::ns16x50::Ns16x50Isr;
use blueos_kconfig::CONFIG_NUM_CORES;
pub(crate) use config::MEMORY_BANKS;
pub use config::{PHYS_DRAM_BASE, PHYS_DRAM_SIZE, TEXT_OFFSET};
pub type ClockImpl = crate::devices::clock::gic_generic_timer::GenericClock;
use alloc::boxed::Box;
use blueos_hal::isr::IsrDesc;

static STAGING: SmpStagedInit = SmpStagedInit::new();

pub(crate) fn init() {
    STAGING.run(0, true, crate::boot::init_runtime);
    STAGING.run(1, true, || {
        cfg_if::cfg_if! {
            if #[cfg(paging)] {
                let regions = crate::mm::memory_bank::create_memory_region_from_memory_bank(
                    crate::boards::MEMORY_BANKS,
                );
                crate::boot::init_frames(&regions);
                crate::mm::kernel_space::init_kernel_space(&regions)
                    .expect("failed to initialize kernel address space");
                crate::allocator::init_paged_heap()
                    .expect("failed to initialize page heap");
            } else {
                crate::boot::init_heap()
            }
        }
    });
    STAGING.run(2, false, || {
        #[cfg(all(paging, smp))]
        if arch::current_cpu_id() != 0 {
            use crate::mm::kernel_space::KernelAddressSpace;
            let space = KernelAddressSpace::get().expect("kernel address space not initialized");
            unsafe { arch::mmu::activate_kernel_table(space.root_address()) };
        }
        arch::vector::init();
    });
    STAGING.run(3, true, || unsafe {
        arch::irq::init(
            config::GICD as u64,
            config::GICR as u64,
            CONFIG_NUM_CORES as usize,
            false,
        )
    });
    STAGING.run(4, false, arch::irq::cpu_init);
    STAGING.run(5, false, || {
        irq::enable_irq_with_priority(
            config::CONSOLE_UART_IRQNUM,
            arch::current_cpu_id(),
            irq::Priority::Normal,
        );
    });
    STAGING.run(6, false, || {
        irq::enable_irq_with_priority(
            config::GENERIC_TIMER_IRQNUM,
            arch::current_cpu_id(),
            irq::Priority::Normal,
        );
    });
    #[cfg(smp)]
    STAGING.run(7, true, || arch::secondary_cpu_setup(config::PSCI_BASE));
    #[cfg(smp)]
    if arch::current_cpu_id() != 0 {
        scheduler::wait_and_then_start_schedule();
        unreachable!("Secondary cores should have jumped to the scheduler");
    }

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
