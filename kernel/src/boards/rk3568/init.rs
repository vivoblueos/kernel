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

use crate::{arch, error::Error, sync::SpinLock, time};
use blueos_kconfig::NUM_CORES;
use core::sync::atomic::Ordering;

pub(crate) fn init() {
    crate::boot::init_runtime();
    crate::boot::init_heap();
    arch::vector::init();
    unsafe { arch::irq::init(config::GICD as u64, config::GICR as u64, NUM_CORES, false) };
    arch::irq::cpu_init();
    time::systick_init(24000000);
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::ns16650::Ns16650,
     blueos_driver::uart::ns16650::Ns16650::new(
        0xFE660000,
     )),
}

crate::define_pin_states!(None);
