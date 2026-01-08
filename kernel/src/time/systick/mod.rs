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

use crate::{
    arch::{self, irq::IrqNumber},
    config, scheduler,
    time::timer,
};
use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicUsize, Ordering},
};

#[cfg(cortex_m)]
include!("cortex_m.rs");
#[cfg(target_arch = "aarch64")]
include!("aarch64.rs");
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
include!("riscv.rs");

pub(crate) static SYSTICK: Systick = Systick::new(SYSTICK_IRQ_NUM);
pub struct Systick {
    tick: AtomicUsize,
    irq_num: IrqNumber,
    step: UnsafeCell<usize>,
}

// SAFETY: step is only written once during initialization and then only read
unsafe impl Sync for Systick {}

impl Systick {
    pub const fn new(irq_num: IrqNumber) -> Self {
        Self {
            irq_num,
            tick: AtomicUsize::new(0),
            step: UnsafeCell::new(0),
        }
    }

    pub fn irq_num(&self) -> IrqNumber {
        self.irq_num
    }

    pub fn get_step(&self) -> usize {
        // SAFETY: step is only read after initialization
        unsafe { *self.step.get() }
    }

    pub fn get_tick(&self) -> usize {
        self.tick.load(Ordering::Relaxed)
    }

    pub fn increment_ticks(&self) -> usize {
        self.tick.fetch_add(1, Ordering::Relaxed) + 1
    }
}
