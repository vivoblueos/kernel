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

use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

use crate::{
    interrupt_controller::Interrupt, static_ref::StaticRef,
    uart::esp32_usb_serial::JFIFO_ST_REG::OUT_FIFO_FULL,
};

register_structs! {
    pub IntcRegisters {
        (0x000 => _reserved0),
        (0x104 => cpu_int_enable_reg: ReadWrite<u32>),
        (0x108 => _reserved1),
        (0x118 => priority_reg: [ReadWrite<u32, PRIORITY_REG::Register>; 31]),
        (0x194 => thresh_reg: ReadWrite<u32, THRESH_REG::Register>),
        (0x198 => @END),
    }
}

register_bitfields! [
    u32,

    pub PRIORITY_REG [
        PRIORITY OFFSET(0) NUMBITS(4) [],
    ],

    pub THRESHOLD_REG [
        THRESHOLD OFFSET(0) NUMBITS(4) [],
    ],
];

pub struct Esp32Intc {
    registers: StaticRef<IntcRegisters>,
}

impl Esp32Intc {
    pub const fn new(base: usize) -> Self {
        Self {
            registers: unsafe { StaticRef::new(base as *const IntcRegisters) },
        }
    }

    pub fn allocate_irq(&self, irq: Interrupt) {
        let mut map_reg =
            self.registers.inner() as *const IntcRegisters as usize + irq.source_no * 4;
        unsafe {
            core::ptr::write_volatile(map_reg as *mut u32, irq.irq_no as u32);
        }
    }

    pub fn enable_irq(&self, irq: Interrupt) {
        let mut enable_reg = self.registers.cpu_int_enable_reg.get();
        enable_reg |= 1 << irq.irq_no;
        self.registers.cpu_int_enable_reg.set(enable_reg);
    }

    pub fn set_priority(&self, irq: Interrupt, priority: u8) {
        self.registers.priority_reg[(irq.irq_no - 1) as usize]
            .write(PRIORITY_REG::PRIORITY.val(priority as u32));
    }

    pub fn set_threshold(&self, threshold: u8) {
        self.registers
            .thresh_reg
            .write(THRESH_REG::THRESH.val(thresh as u32));
    }
}
