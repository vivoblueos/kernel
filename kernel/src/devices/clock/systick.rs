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

use crate::{arch, arch::irq::IRQ_PRIORITY_FOR_SCHEDULER, devices::clock::Clock};
use core::sync::atomic::{AtomicUsize, Ordering};
use cortex_m::peripheral::{scb::SystemHandler, syst::SystClkSource, SCB, SYST};

// A SysTick device is a built-in, 24-bit system timer in ARM Cortex-M
// processors, acting as a simple, precise hardware timer for generating
// periodic interrupts, creating delays, or serving real-time operating systems
// (RTOS) by counting down from a set value and reloading, providing essential
// timing for embedded applications.
pub struct SysTickClock<const TICKS_PS: usize, const HZ: usize>;
// We're using a count-down clock to emulate a monotonic clock. That's to say
// the counter is emulated and is maintained by software.
static TICKS: AtomicUsize = AtomicUsize::new(0);
static INTERRUPT_AT: AtomicUsize = AtomicUsize::new(0);

// Use SysTick's count-down counter to simulate a monotonith counter.
impl<const TICKS_PS: usize, const HZ: usize> Clock for SysTickClock<TICKS_PS, HZ> {
    // We are making 1cycle == 1tick virtually.
    fn hz() -> u64 {
        TICKS_PS as u64
    }

    fn estimate_current_cycles() -> u64 {
        TICKS.load(Ordering::Relaxed) as u64
    }

    fn interrupt_at(nth: u64) {
        INTERRUPT_AT.store(nth as usize, Ordering::Relaxed);
        if TICKS.load(Ordering::Relaxed) < nth as usize {
            return;
        }
        SCB::set_pendst();
        unsafe { core::arch::asm!("isb", options(nostack),) };
    }

    fn stop() {
        INTERRUPT_AT.store(usize::MAX, Ordering::Relaxed)
    }
}

impl<const TICKS_PS: usize, const HZ: usize> SysTickClock<TICKS_PS, HZ> {
    fn systick() -> SYST {
        unsafe { core::mem::transmute::<(), SYST>(()) }
    }

    fn scb() -> SCB {
        unsafe { core::mem::transmute::<(), SCB>(()) }
    }

    pub fn init() {
        debug_assert_eq!(HZ % TICKS_PS, 0);
        let reload = (HZ / TICKS_PS) as u32;
        debug_assert!(reload <= 0x00ff_ffff);
        debug_assert!(reload > 0);
        let mut scb = Self::scb();
        unsafe { scb.set_priority(SystemHandler::SysTick, IRQ_PRIORITY_FOR_SCHEDULER) };
        let mut systick = Self::systick();
        systick.disable_counter();
        systick.set_clock_source(SystClkSource::Core);
        systick.set_reload(reload);
        systick.clear_current();
        systick.enable_counter();
        systick.enable_interrupt();
    }

    pub fn on_interrupt() {
        let now = if Self::systick().has_wrapped() {
            TICKS.fetch_add(1, Ordering::Relaxed) + 1
        } else {
            // In case pend_st is manually called.
            TICKS.load(Ordering::Relaxed)
        };
        if now < INTERRUPT_AT.load(Ordering::Relaxed) {
            return;
        }
        crate::time::handle_clock_interrupt();
    }
}
