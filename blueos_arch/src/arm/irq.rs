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

#[cfg(irq_priority_bits_2)]
pub const IRQ_PRIORITY_STEP: u8 = 0x40;
#[cfg(irq_priority_bits_3)]
pub const IRQ_PRIORITY_STEP: u8 = 0x20;
#[cfg(irq_priority_bits_8)]
pub const IRQ_PRIORITY_STEP: u8 = 0x10;

#[cfg(irq_priority_bits_2)]
pub const IRQ_PRIORITY_FOR_SCHEDULER: u8 = 0x80;
#[cfg(irq_priority_bits_3)]
pub const IRQ_PRIORITY_FOR_SCHEDULER: u8 = 0x40;
#[cfg(irq_priority_bits_8)]
pub const IRQ_PRIORITY_FOR_SCHEDULER: u8 = 0x20;

pub const SVC_PRIORITY: u8 = IRQ_PRIORITY_FOR_SCHEDULER - IRQ_PRIORITY_STEP;

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum Priority {
    // can't use ipc in high priority irq
    High = IRQ_PRIORITY_FOR_SCHEDULER - IRQ_PRIORITY_STEP * 2,
    Normal = IRQ_PRIORITY_FOR_SCHEDULER,
    Low = IRQ_PRIORITY_FOR_SCHEDULER + IRQ_PRIORITY_STEP,
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct IrqNumber(u16);

impl IrqNumber {
    #[inline]
    pub const fn new(number: u16) -> Self {
        Self(number)
    }

    #[inline]
    pub fn get(self) -> u16 {
        self.0
    }
}

impl From<IrqNumber> for usize {
    fn from(irq: IrqNumber) -> Self {
        usize::from(irq.0)
    }
}

// SAFETY: get the number of the interrupt is safe
unsafe impl cortex_m::interrupt::InterruptNumber for IrqNumber {
    #[inline]
    fn number(self) -> u16 {
        self.0
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub union Vector {
    pub handler: unsafe extern "C" fn(),
    pub reserved: usize,
}

pub const INTERRUPT_TABLE_LEN: usize = blueos_kconfig::CONFIG_NUM_IRQS as usize;