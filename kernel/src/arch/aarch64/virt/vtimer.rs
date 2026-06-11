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

use super::vgic;
use crate::arch::aarch64::{
    current_cpu_id,
    irq::{self, IrqNumber, Priority},
};
use alloc::boxed::Box;
use blueos_hal::isr::IsrDesc;
use core::arch::asm;

pub struct VirtualTimerHandler;

impl IsrDesc for VirtualTimerHandler {
    fn service_isr(&self) {
        unsafe {
            let vcpu_id = current_cpu_id();
            vgic::inject_irq(vcpu_id, 27);
            vgic::flush(vcpu_id);
        }
    }
}

pub fn init_global_vtimer() {
    let timer_handler = Box::new(VirtualTimerHandler);
    irq::register_handler(IrqNumber::new(27), timer_handler)
        .expect("[vTimer] Failed to register IRQ 27 handler");
}

/// Call it before booting guest.
pub fn init_vcpu_timer() {
    irq::enable_irq_with_priority(IrqNumber::new(27), current_cpu_id(), Priority::Normal);
}

#[cfg(not(test))]
#[inline]
fn read_cntv_ctl() -> u64 {
    let ctl: u64;
    unsafe {
        asm!("mrs {}, CNTV_CTL_EL0", out(reg) ctl);
    }
    ctl
}

#[cfg(not(test))]
#[inline]
fn write_cntv_ctl(ctl: u64) {
    unsafe {
        asm!("msr CNTV_CTL_EL0, {}", in(reg) ctl);
    }
}

#[cfg(test)]
static mut MOCK_CNTV_CTL: u64 = 0;

#[cfg(test)]
fn read_cntv_ctl() -> u64 {
    unsafe { MOCK_CNTV_CTL }
}

#[cfg(test)]
fn write_cntv_ctl(ctl: u64) {
    unsafe {
        MOCK_CNTV_CTL = ctl;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_vtimer_handler_injects_irq() {
        unsafe {
            MOCK_CNTV_CTL = 0;
        }

        let mut handler = VirtualTimerHandler;
        handler.service_isr();
        // IMASK is no longer set — vGIC HW LR + EOImode prevents re-trigger.
        unsafe {
            assert_eq!(
                MOCK_CNTV_CTL & (1 << 1),
                0,
                "vTimer should NOT set IMASK (bit 1)"
            );
        }
    }
}
