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

extern crate alloc;

use crate::sync::SpinLock;
use alloc::boxed::Box;
use blueos_hal::isr::IsrDesc;

pub use bluekernel_arch::aarch64::irq::{
    cpu_init, disable_irq, enable_irq, enable_irq_with_priority, end_interrupt, get_interrupt,
    init, send_sgi, set_irq_priority, set_priority_mask, set_trigger, IrqNumber, IrqTrigger,
    Priority, INTERRUPT_TABLE_LEN, SPECIAL_NONE,
};

pub struct IrqContext {
    pub irq: IrqNumber,
    pub handler: Box<dyn IsrDesc>,
}

impl core::fmt::Display for IrqContext {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "IRQ {:?} -> Handler@{:p}", self.irq, self.handler)
    }
}

impl IrqContext {
    fn new(irq: IrqNumber, handler: Box<dyn IsrDesc>) -> Self {
        Self { irq, handler }
    }
}

pub struct IrqManager {
    pub contexts: [Option<IrqContext>; INTERRUPT_TABLE_LEN],
}

pub static IRQ_MANAGER: SpinLock<IrqManager> = SpinLock::new(IrqManager::new());

impl IrqManager {
    const fn new() -> Self {
        const NONE_CONTEXT: Option<IrqContext> = None;
        Self {
            contexts: [NONE_CONTEXT; INTERRUPT_TABLE_LEN],
        }
    }

    fn register_handler(
        &mut self,
        irq: IrqNumber,
        handler: Box<dyn IsrDesc>,
    ) -> Result<(), &'static str> {
        if u32::from(irq) >= INTERRUPT_TABLE_LEN as u32 {
            return Err("IRQ number out of range");
        }
        self.contexts[usize::from(irq)] = Some(IrqContext::new(irq, handler));
        Ok(())
    }

    fn trigger_irq(&mut self, irq: IrqNumber) -> Result<(), &'static str> {
        if let Some(context) = &mut self.contexts[usize::from(irq)] {
            context.handler.service_isr();
            return Ok(());
        }
        Err("handler not found")
    }
}

pub fn register_handler(irq: IrqNumber, handler: Box<dyn IsrDesc>) -> Result<(), &'static str> {
    IRQ_MANAGER.lock().register_handler(irq, handler)
}

pub fn trigger_irq(irq: IrqNumber) -> Result<(), &'static str> {
    IRQ_MANAGER.lock().trigger_irq(irq)
}
