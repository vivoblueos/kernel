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

// TODO: Use safe_mmio.

use crate::arch::riscv64;

pub(crate) type CallbackFn = extern "C" fn(irqno: usize) -> i32;

pub struct Plic {
    base: *mut u32,
}

impl Plic {
    pub const fn new(base: usize) -> Self {
        Self {
            base: unsafe { base as *mut u32 },
        }
    }

    pub fn init(&self) {}

    pub fn set_priority(&self, irq: u32, prio: u32) {
        assert!(irq > 0);
        unsafe { self.base.offset(irq as isize).write_volatile(prio) };
    }

    pub fn enable(&self, cpu_id: usize, irq: u32) {
        let hart = cpu_id as isize;
        unsafe {
            let ptr = self
                .base
                .byte_offset(0x2000)
                .byte_offset(hart * 0x80)
                .offset(irq as isize / 32);
            let old = ptr.read_volatile();
            ptr.write_volatile(old | (1 << (irq % 32)));
        }
    }

    pub fn disable(&self, cpu_id: usize, irq: u32) {
        let hart = cpu_id as isize;
        unsafe {
            let ptr = self
                .base
                .byte_offset(0x2000)
                .byte_offset(hart * 0x80)
                .offset(irq as isize / 32);
            let old = ptr.read_volatile();
            ptr.write_volatile(old & !(1 << (irq % 32)));
        }
    }

    pub fn claim(&self, cpu_id: usize) -> u32 {
        let hart = cpu_id as isize;
        unsafe {
            self.base
                .byte_offset(0x20_0004)
                .byte_offset(hart * 0x1000)
                .read_volatile()
        }
    }

    pub fn complete(&self, cpu_id: usize, irq: u32) {
        let hart = cpu_id as isize;
        unsafe {
            self.base
                .byte_offset(0x20_0004)
                .byte_offset(hart * 0x1000)
                .write_volatile(irq)
        }
    }

    pub fn set_threshold(&self, cpu_id: usize, val: u32) {
        let hart = cpu_id as isize;
        unsafe {
            self.base
                .byte_offset(0x20_0000)
                .byte_offset(hart * 0x1000)
                .write_volatile(val);
        }
    }
}

unsafe impl Sync for Plic {}
