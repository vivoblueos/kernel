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

use super::{config, uart};
use crate::{
    arch::{self, READY_CORES},
    devices::{console, tty::n_tty::Tty},
    error::Error,
    scheduler,
    support::SmpStagedInit,
    time,
};
use alloc::sync::Arc;
use blueos_kconfig::NUM_CORES;
use core::sync::atomic::Ordering;

static STAGING: SmpStagedInit = SmpStagedInit::new();

// only primary core will run this function
// secondary cores now park by entry code
pub(crate) fn init() {
    STAGING.run(0, true, || crate::boot::init_runtime());
    STAGING.run(1, true, || crate::boot::init_heap());
    STAGING.run(2, true, || arch::vector::init());
    STAGING.run(3, true, || unsafe {
        arch::irq::init(config::GICD as u64, config::GICC as u64)
    });
    STAGING.run(4, true, || arch::irq::cpu_init());
    STAGING.run(5, true, || {
        time::systick_init(0);
    });
    STAGING.run(6, true, || {
        uart::enable_uart(arch::current_cpu_id());
    });
    // #TODO: Enable PSCI for secondary cores
    // This is a temporary solution for BCM2711
    STAGING.run(7, true, || {
        // Initialize the console and UART
        match uart::uart_init() {
            Ok(_) => (),
            Err(e) => panic!("Failed to init uart: {}", Error::from(e)),
        }
        match console::init_console(Tty::init(uart::get_serial0().clone()).clone()) {
            Ok(_) => (),
            Err(e) => panic!("Failed to init console: {}", Error::from(e)),
        }
    });

    // Configure GPIO for UART
    // use bootloader's config.txt to set up GPIO
    // GPIO14 and GPIO15 are used for UART0 TX and RX respectively
    // uart::init_gpio();
}

fn wait_and_then_start_schedule() {
    while READY_CORES.load(Ordering::Acquire) == 0 {
        core::hint::spin_loop();
    }
    arch::start_schedule(scheduler::schedule);
}
