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
#[cfg(virtio)]
use super::uart::{enable_uart, get_serial};
use crate::{
    arch::{self, READY_CORES},
    devices::{console, tty::n_tty::Tty, virtio},
    error::Error,
    scheduler,
    support::SmpStagedInit,
    time,
};
use alloc::{string::String, sync::Arc};
use blueos_kconfig::NUM_CORES;
use core::sync::atomic::Ordering;
#[cfg(virtio)]
use flat_device_tree::Fdt;

static STAGING: SmpStagedInit = SmpStagedInit::new();

pub(crate) fn init() {
    STAGING.run(0, true, || crate::boot::init_runtime());
    STAGING.run(1, true, || crate::boot::init_heap());
    STAGING.run(2, false, || arch::vector::init());
    STAGING.run(3, true, || unsafe {
        arch::irq::init(config::GICD as u64, config::GICR as u64, NUM_CORES, false)
    });
    STAGING.run(4, false, || arch::irq::cpu_init());
    STAGING.run(5, false, || {
        time::systick_init(0);
    });
    STAGING.run(6, false, || {
        enable_uart(arch::current_cpu_id(), config::PL011_UART0_IRQNUM);
    });
    STAGING.run(7, true, || arch::secondary_cpu_setup(config::PSCI_BASE));
    if arch::current_cpu_id() != 0 {
        wait_and_then_start_schedule();
        unreachable!("Secondary cores should have jumped to the scheduler");
    }

    match super::uart::uart_init(
        0,
        config::PL011_UART0_BASE,
        config::APBP_CLOCK,
        config::PL011_UART0_IRQNUM,
        String::from("ttyS0"),
    ) {
        Ok(_) => (),
        Err(e) => panic!("Failed to init uart: {}", Error::from(e)),
    }
    match console::init_console(Tty::init(get_serial(0).clone()).clone()) {
        Ok(_) => (),
        Err(e) => panic!("Failed to init console: {}", Error::from(e)),
    }
    #[cfg(virtio)]
    {
        // initialize fdt
        // SAFETY: We trust that the FDT pointer we were given is valid, and this is the only time we
        // use it.
        let fdt = unsafe { Fdt::from_ptr(config::DRAM_BASE as *const u8).unwrap() };
        // initialize virtio
        virtio::init_virtio(&fdt);
    }
}

fn wait_and_then_start_schedule() {
    while READY_CORES.load(Ordering::Acquire) == 0 {
        core::hint::spin_loop();
    }
    arch::start_schedule(scheduler::schedule);
}
