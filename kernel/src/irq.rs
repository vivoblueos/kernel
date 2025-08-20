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

use crate::{arch, support::DisableInterruptGuard, time, types::Uint};
use blueos_kconfig::NUM_CORES;
use core::sync::atomic::Ordering;

// Nesting level might not be very large, use AtomicUint here.
pub(crate) static mut IRQ_NESTING_COUNT: [Uint; NUM_CORES] = [const { 0 }; NUM_CORES];

pub struct IrqTrace {
    irq_number: arch::irq::IrqNumber,
}

impl IrqTrace {
    pub fn new(irq_number: arch::irq::IrqNumber) -> Self {
        let irq_trace = Self { irq_number };
        irq_trace.enter();
        irq_trace
    }

    #[inline]
    fn enter(&self) {
        enter_irq();
        #[cfg(procfs)]
        unsafe {
            irq_trace::IRQ_COUNTERS[usize::from(self.irq_number)].fetch_add(1, Ordering::Relaxed);
        }
    }

    #[inline]
    fn leave(&self) {
        leave_irq();
    }
}

impl Drop for IrqTrace {
    fn drop(&mut self) {
        self.leave();
    }
}

pub fn is_in_irq() -> bool {
    let _dig = DisableInterruptGuard::new();
    unsafe { IRQ_NESTING_COUNT[arch::current_cpu_id()] != 0 }
}

#[inline]
unsafe fn increment_nesting_count() -> usize {
    let id = arch::current_cpu_id();
    let old = IRQ_NESTING_COUNT[id];
    let _ = core::mem::replace(&mut IRQ_NESTING_COUNT[id], old + 1);
    old as usize
}

#[inline]
unsafe fn decrement_nesting_count() -> usize {
    let id = arch::current_cpu_id();
    let old = IRQ_NESTING_COUNT[id];
    let _ = core::mem::replace(&mut IRQ_NESTING_COUNT[id], old - 1);
    old as usize
}

// This might be called from assembly code, use extern "C" here.
pub extern "C" fn enter_irq() -> usize {
    let _dig = DisableInterruptGuard::new();
    #[cfg(procfs)]
    unsafe {
        irq_trace::PER_CPU_TRACE_INFO[arch::current_cpu_id()].on_enter();
    }
    unsafe { increment_nesting_count() + 1 }
}

pub extern "C" fn leave_irq() -> usize {
    let _dig = DisableInterruptGuard::new();
    #[cfg(procfs)]
    unsafe {
        irq_trace::PER_CPU_TRACE_INFO[arch::current_cpu_id()].on_leave();
    }
    unsafe { decrement_nesting_count() - 1 }
}

#[cfg(procfs)]
pub mod irq_trace {
    use crate::{arch::irq::INTERRUPT_TABLE_LEN, time};
    use blueos_kconfig::NUM_CORES;
    use core::sync::atomic::AtomicUsize;

    pub static IRQ_COUNTERS: [AtomicUsize; INTERRUPT_TABLE_LEN] =
        [const { AtomicUsize::new(0) }; INTERRUPT_TABLE_LEN];

    pub static mut PER_CPU_TRACE_INFO: [IrqTraceInfo; NUM_CORES] = {
        [const {
            IrqTraceInfo {
                last_irq_enter_cycles: 0,
                total_irq_process_cycles: 0,
            }
        }; NUM_CORES]
    };

    pub struct IrqTraceInfo {
        pub last_irq_enter_cycles: u64,
        pub total_irq_process_cycles: u64,
    }

    impl IrqTraceInfo {
        #[inline]
        pub fn on_enter(&mut self) {
            self.last_irq_enter_cycles = time::get_sys_cycles();
        }

        #[inline]
        pub fn on_leave(&mut self) {
            let current_cycles = time::get_sys_cycles();
            self.total_irq_process_cycles =
                current_cycles.saturating_sub(self.last_irq_enter_cycles);
        }
    }
}
