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

use crate::cortex_m::{nvic, scb, scb::SystemHandler, xpsr};
use blueos_hal::isr::{IsrDesc, IsrReg};

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
    // Can't use IPC in high priority IRQ.
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
}

impl From<IrqNumber> for usize {
    fn from(irq: IrqNumber) -> Self {
        usize::from(irq.0)
    }
}

pub fn init() {
    // Safety: system handler priorities are set during early IRQ init before
    // normal scheduling and priority-based critical sections are active.
    unsafe {
        scb::set_system_handler_priority(SystemHandler::SVCall, SVC_PRIORITY);
        scb::set_system_handler_priority(SystemHandler::PendSV, IRQ_PRIORITY_FOR_SCHEDULER);
    }
}

pub fn enable_irq_with_priority(irq: IrqNumber, priority: Priority) {
    set_irq_priority(irq, priority as u8);
    unsafe { nvic::enable(irq.0) };
}

pub fn enable_irq(irq: IrqNumber) {
    unsafe { nvic::enable(irq.0) };
}

pub fn disable_irq(irq: IrqNumber) {
    unsafe { nvic::disable(irq.0) };
}

pub fn is_irq_enabled(irq: IrqNumber) -> bool {
    unsafe { nvic::is_enabled(irq.0) }
}

pub fn is_irq_active(irq: IrqNumber) -> bool {
    unsafe { nvic::is_active(irq.0) }
}

pub fn get_irq_priority(irq: IrqNumber) -> u8 {
    unsafe { nvic::get_priority(irq.0) }
}

pub fn set_irq_priority(irq: IrqNumber, priority: u8) {
    unsafe { nvic::set_priority(irq.0, priority) };
}

#[derive(Clone, Copy)]
#[repr(C)]
pub union Vector {
    pub handler: unsafe extern "C" fn(),
    pub reserved: usize,
}

pub const INTERRUPT_TABLE_LEN: usize = blueos_kconfig::CONFIG_NUM_IRQS as usize;

/// Interrupt vector table configuration for ARM Cortex-M processors.
///
/// There are two types of ISRs, one is the RAW type, which is no different
/// from general interrupt service handling. The other is the more flexible
/// SWI type. SWI type interrupt service handling implements the trait object
/// IsrDesc. For some complex processing scenarios, consider using IsrDesc
/// to encapsulate relevant data, such as Shared ISR, Async ISR, Nested ISR,
/// and so on.
///
/// # Safety
///
/// The interrupt vector table must be properly aligned and contain valid
/// function pointers for all used interrupt vectors. Incorrect configuration
/// may lead to undefined behavior.
#[used]
#[link_section = ".interrupt.handlers"]
static mut __INTERRUPT_HANDLERS__: [Vector; blueos_kconfig::CONFIG_NUM_IRQS as usize] = [Vector {
    handler: _generic_isr_handler,
};
    INTERRUPT_TABLE_LEN];

extern "C" fn _generic_isr_handler() {
    // Safety: this handler runs on Cortex-M exception entry; xPSR carries the
    // same active exception number previously read from IPSR directly.
    let xpsr = unsafe { xpsr::read() };
    let isr_index = xpsr
        .external_interrupt_number()
        .expect("Invalid ISR index, xPSR does not identify an external interrupt");

    if let Some(isr_desc) = unsafe { ISR_DESC[isr_index as usize].as_ref() } {
        isr_desc.service_isr();
    } else {
        // FIXME: If the ISR is not explicitly registered, what should be done?
    }

    #[cfg(round_robin)]
    {
        // If the scheduler is preemptive, trigger PendSV to perform a context
        // switch after handling the current interrupt. External interrupts
        // firing before the scheduler is ready are unsupported and would be
        // undefined for BlueOS; that boot-time ordering violation should not
        // happen. PendSV still keeps the final readiness guard before touching
        // PSP or scheduler task queues.
        unsafe { scb::set_pendsv() };
    }
}

static mut ISR_DESC: [Option<&dyn IsrDesc>; INTERRUPT_TABLE_LEN] = [None; INTERRUPT_TABLE_LEN];

/// Safety: ISR_DESC only be read in the interrupt handler,
/// and only be written in the boot process early, so it's
/// safe to use unsafe to write it.
pub fn init_interrupt_registry() {
    extern "C" {
        static __isr_array_start: usize;
        static __isr_array_end: usize;
    }

    unsafe {
        let mut p = core::ptr::addr_of!(__isr_array_start);
        while p < core::ptr::addr_of!(__isr_array_end) {
            let r = &*(p as *const IsrReg);
            assert!(
                r.no < INTERRUPT_TABLE_LEN,
                "ISR number {} exceeds the maximum limit {}",
                r.no,
                INTERRUPT_TABLE_LEN
            );
            ISR_DESC[r.no] = Some(r.desc);
            p = (p as *const IsrReg).offset(1) as *const usize;
        }
    }
}

/// This function is used to register the raw interrupt handler for the given
/// IRQ number. The handler should be defined in the assembly file, and the
/// caller should ensure that the handler is properly defined and linked.
///
/// # Safety
///
/// Race condition may occur if this function is called while the corresponding
/// interrupt is enabled and can be triggered, so the caller should ensure that
/// the interrupt is disabled before calling this function, and enable it after
/// the handler is registered.
pub unsafe fn register_raw_isr(irq: IrqNumber, handler: unsafe extern "C" fn()) {
    __INTERRUPT_HANDLERS__[irq.0 as usize] = Vector { handler };
}
