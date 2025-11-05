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

use cortex_m::{interrupt::InterruptNumber, peripheral::scb::SystemHandler, Peripherals};

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
}

impl From<IrqNumber> for usize {
    fn from(irq: IrqNumber) -> Self {
        usize::from(irq.0)
    }
}

// SAFETY: get the number of the interrupt is safe
unsafe impl InterruptNumber for IrqNumber {
    #[inline]
    fn number(self) -> u16 {
        self.0
    }
}

pub fn init() {
    // SAFETY: steal and set the peripherals in init is safe
    unsafe {
        let mut scb = Peripherals::steal();
        scb.SCB.set_priority(SystemHandler::SVCall, SVC_PRIORITY);
        scb.SCB
            .set_priority(SystemHandler::PendSV, IRQ_PRIORITY_FOR_SCHEDULER);
    }
}

pub fn enable_irq_with_priority(irq: IrqNumber, priority: Priority) {
    set_irq_priority(irq, priority as u8);
    unsafe { cortex_m::peripheral::NVIC::unmask(irq) };
}

pub fn enable_irq(irq: IrqNumber) {
    unsafe { cortex_m::peripheral::NVIC::unmask(irq) };
}

pub fn disable_irq(irq: IrqNumber) {
    unsafe { cortex_m::peripheral::NVIC::mask(irq) };
}

pub fn is_irq_enabled(irq: IrqNumber) -> bool {
    unsafe { cortex_m::peripheral::NVIC::is_enabled(irq) }
}

pub fn is_irq_active(irq: IrqNumber) -> bool {
    unsafe { cortex_m::peripheral::NVIC::is_active(irq) }
}

pub fn get_irq_priority(irq: IrqNumber) -> u8 {
    unsafe { cortex_m::peripheral::NVIC::get_priority(irq) }
}

pub fn set_irq_priority(irq: IrqNumber, priority: u8) {
    unsafe {
        cortex_m::Peripherals::steal()
            .NVIC
            .set_priority(irq, priority)
    };
}

#[derive(Clone, Copy)]
#[repr(C)]
pub union Vector {
    pub handler: unsafe extern "C" fn(),
    pub reserved: usize,
}

/// Interrupt vector table configuration for ARM Cortex-M processors.
///
/// Users must define their own `__INTERRUPTS` based on their specific device requirements.
/// The interrupt vector table should be placed in the `.vector_table.interrupts` section.
///
/// # Example
///
/// ```rust
///
/// #[used]
/// #[link_section = ".interrupt.vectors"]
/// #[no_mangle]
/// pub static __INTERRUPT_HANDLERS__: InterruptTable = {
///     let mut tbl = [Vector { reserved: 0 }; INTERRUPT_TABLE_LEN];
///     tbl[0] = Vector {
///         handler: uart0rx_handler,
///     };
///     tbl[1] = Vector {
///         handler: uart0tx_handler,
///     };
///     tbl[2] = Vector {
///         handler: uart1rx_handler,
///     };
///     tbl
/// };
///
/// // Declare external interrupt handlers
/// extern "C" {
///     fn uart0rx_handler();
///     fn uart0tx_handler();
///     fn uart1rx_handler();
/// }
/// ```
///
/// # Architecture-specific Details
///
/// Maximum number of device-specific interrupts for different ARM Cortex-M architectures:
/// - ARMv6-M: 32 interrupts
/// - ARMv7-M/ARMv7E-M: 240 interrupts
/// - ARMv8-M: 496 interrupts
///
/// # Safety
///
/// The interrupt vector table must be properly aligned and contain valid function pointers
/// for all used interrupt vectors. Incorrect configuration may lead to undefined behavior.
#[cfg(armv6m)]
pub const INTERRUPT_TABLE_LEN: usize = 32;
#[cfg(any(armv7m, armv7em))]
pub const INTERRUPT_TABLE_LEN: usize = 240;
#[cfg(armv8m)]
pub const INTERRUPT_TABLE_LEN: usize = 496;
pub type InterruptTable = [Vector; INTERRUPT_TABLE_LEN];
