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

pub use arm_gic::Trigger as IrqTrigger;
use arm_gic::{gicv3::*, IntId};
use spin::{Mutex, Once};

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum Priority {
    High = 0x10,
    Normal = 0x80,
    Low = 0xf0,
}

const PPI_START: u32 = 16;
const SPI_START: u32 = 32;
pub const SPECIAL_NONE: u32 = 1023;

static GIC: Once<Mutex<GicV3>> = Once::new();

#[derive(Debug, Copy, Clone, Eq, Ord, PartialOrd, PartialEq)]
#[repr(transparent)]
pub struct IrqNumber(IntId);

impl IrqNumber {
    pub const fn new(irq: u32) -> Self {
        let id = match irq {
            0..PPI_START => IntId::sgi(irq),
            PPI_START..SPI_START => IntId::ppi(irq - PPI_START),
            _ => IntId::spi(irq - SPI_START),
        };
        Self(id)
    }

    pub const fn from_raw_id(raw: u32) -> Self {
        let id = match raw {
            0..PPI_START => IntId::sgi(raw),
            PPI_START..SPI_START => IntId::ppi(raw - PPI_START),
            SPECIAL_NONE => IntId::SPECIAL_NONE,
            _ => IntId::spi(raw - SPI_START),
        };
        Self(id)
    }
}

impl From<IrqNumber> for u32 {
    fn from(irq: IrqNumber) -> Self {
        u32::from(irq.0)
    }
}

impl From<IrqNumber> for usize {
    fn from(irq: IrqNumber) -> Self {
        u32::from(irq.0) as usize
    }
}

pub unsafe fn init(gicd: u64, gicr: u64, num_cores: usize, is_v4: bool) {
    GIC.call_once(|| {
        let gic = unsafe {
            GicV3::new(
                gicd as *mut u64 as _,
                gicr as *mut u64 as _,
                num_cores,
                is_v4,
            )
        };
        Mutex::new(gic)
    });
}

pub fn cpu_init() {
    with_gic(|gic| gic.setup(current_cpu_id()));
    set_priority_mask(0xff);
}

fn get_gic() -> &'static Mutex<GicV3<'static>> {
    GIC.get().unwrap()
}

fn with_gic<R>(f: impl FnOnce(&mut GicV3<'static>) -> R) -> R {
    // The old kernel-side GIC manager used SpinLock::irqsave_lock(). After
    // moving the GIC object into bluekernel_arch we cannot depend on that
    // kernel lock type, so keep the same critical-section shape locally:
    // save DAIF, mask IRQ/FIQ while the raw spin::Mutex is held, then restore
    // the previous interrupt mask exactly.
    let state = local_irq_save();
    let mut gic = get_gic().lock();
    let result = f(&mut gic);
    local_irq_restore(state);
    result
}

#[inline]
fn local_irq_save() -> u64 {
    let state: u64;
    unsafe {
        core::arch::asm!(
            "mrs {state}, daif",
            "msr daifset, #3",
            state = out(reg) state,
            options(nostack)
        );
    }
    state
}

#[inline]
fn local_irq_restore(state: u64) {
    unsafe { core::arch::asm!("msr daif, {state}", state = in(reg) state, options(nostack)) };
}

#[inline]
fn current_cpu_id() -> usize {
    let mpidr: usize;
    unsafe { core::arch::asm!("mrs {}, mpidr_el1", out(reg) mpidr, options(nostack)) };
    mpidr & 0xff
}

pub const INTERRUPT_TABLE_LEN: usize = 1024;

pub fn enable_irq_with_priority(irq: IrqNumber, cpu_id: usize, priority: Priority) {
    with_gic(|gic| {
        gic.set_interrupt_priority(irq.0, Some(cpu_id), priority as u8);
        gic.enable_interrupt(irq.0, Some(cpu_id), true);
    });
}

pub fn enable_irq(irq: IrqNumber, cpu_id: usize) {
    with_gic(|gic| gic.enable_interrupt(irq.0, Some(cpu_id), true));
}

pub fn disable_irq(irq: IrqNumber, cpu_id: usize) {
    with_gic(|gic| gic.enable_interrupt(irq.0, Some(cpu_id), false));
}

pub fn set_irq_priority(irq: IrqNumber, cpu_id: usize, priority: u8) {
    with_gic(|gic| gic.set_interrupt_priority(irq.0, Some(cpu_id), priority));
}

pub fn set_priority_mask(priority: u8) {
    GicV3::set_priority_mask(priority);
}

pub fn set_trigger(irq: IrqNumber, cpu_id: usize, trigger: IrqTrigger) {
    with_gic(|gic| gic.set_trigger(irq.0, Some(cpu_id), trigger));
}

pub fn get_interrupt() -> IrqNumber {
    match GicV3::get_and_acknowledge_interrupt() {
        None => IrqNumber(IntId::SPECIAL_NONE),
        Some(intid) => IrqNumber(intid),
    }
}

pub fn end_interrupt(irq: IrqNumber) {
    GicV3::end_interrupt(irq.0);
}

pub fn send_sgi(irq: IrqNumber, cpu_mask: u16) {
    GicV3::send_sgi(
        irq.0,
        SgiTarget::List {
            affinity3: 0,
            affinity2: 0,
            affinity1: 0,
            target_list: cpu_mask,
        },
    );
}
