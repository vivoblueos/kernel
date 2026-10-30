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

// GICv3 and GICv2 defines the IRQ number of the generic timer.
pub const IRQ_NUMBER: usize = 30;

pub struct GenericTimer;

impl GenericTimer {
    pub const fn new() -> Self {
        Self {}
    }

    pub fn init() {}

    #[inline(always)]
    pub fn read_cntfrq() -> u64 {
        let val: u64;
        unsafe {
            core::arch::asm!("mrs {}, cntfrq_el0", out(reg) val, options(nomem, nostack));
        }
        val
    }

    #[inline(always)]
    pub fn read_cntpct() -> u64 {
        let val: u64;
        unsafe {
            core::arch::asm!("isb; mrs {}, cntpct_el0", out(reg) val, options(nomem, nostack));
        }
        val
    }

    #[inline(always)]
    pub fn write_cntp_cval(val: u64) {
        unsafe {
            core::arch::asm!("msr cntp_cval_el0, {}", in(reg) val, options(nomem, nostack));
        }
    }

    /// Bit 0: ENABLE (1 = enabled)
    /// Bit 1: IMASK  (1 = interrupt masked/disabled, 0 = interrupt unmasked/enabled)
    /// Bit 2: ISTATUS (Read-only)
    #[inline(always)]
    pub fn write_cntp_ctl(val: u64) {
        unsafe {
            core::arch::asm!("msr cntp_ctl_el0, {}", in(reg) val, options(nomem, nostack));
        }
    }
}
