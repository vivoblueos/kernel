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

use crate::arch::aarch64::{
    registers::hcr_el2::HCR_EL2,
    registers::sctlr_el2::SCTLR_EL2,
    registers::spsr_el2::SPSR_EL2,
    virt::vector,
    virt::mmu_el2
};
use tock_registers::interfaces::{Readable, Writeable};

#[inline]
pub fn get_current_el() -> u64 {
    let current_el: u64;
    unsafe {
        core::arch::asm!("mrs {}, currentel", out(reg) current_el);
    }
    (current_el >> 2) & 0x3
}

#[inline]
pub fn read_hcr_el2() -> u64 {
    HCR_EL2.get()
}

#[inline]
pub fn write_hcr_el2(val: u64) {
    HCR_EL2.set(val);
}

#[inline]
pub fn read_vbar_el2() -> u64 {
    let vbar: u64;
    unsafe {
        core::arch::asm!("mrs {}, vbar_el2", out(reg) vbar);
    }
    vbar
}

#[inline]
pub fn write_vbar_el2(val: u64) {
    unsafe {
        core::arch::asm!("msr vbar_el2, {}", in(reg) val);
    }
}

#[inline]
pub fn read_esr_el2() -> u64 {
    let esr: u64;
    unsafe {
        core::arch::asm!("mrs {}, esr_el2", out(reg) esr);
    }
    esr
}

#[inline]
pub fn read_elr_el2() -> u64 {
    let elr: u64;
    unsafe {
        core::arch::asm!("mrs {}, elr_el2", out(reg) elr);
    }
    elr
}

#[inline]
fn configure_hcr_el2() {
    HCR_EL2.write(HCR_EL2::RW::EL1AArch64);
}

#[inline]
pub fn read_spsr_el2() -> u64 {
    let spsr: u64;
    unsafe {
        core::arch::asm!("mrs {}, spsr_el2", out(reg) spsr);
    }
    spsr
}

#[inline]
pub fn configure_hcr_el2_for_guest() {
    // Identity map 192MB of RAM starting from 0x4400_0000 so the Guest can run in-place
    super::mmu_s2::init_stage2(0x4400_0000, 0x0c00_0000); 
    HCR_EL2.write(
        HCR_EL2::VM::Enable
            + HCR_EL2::RW::EL1AArch64
            + HCR_EL2::IMO::EL2Handled
            + HCR_EL2::FMO::EL2Handled
            + HCR_EL2::AMO::EL2Handled
            + HCR_EL2::TSC::Trap
    );
    unsafe {
        core::arch::asm!("isb");
    }
}

#[inline]
fn configure_vector_table(vector_base: usize) {
    unsafe {
        core::arch::asm!(
            "msr vbar_el2, {}",
            in(reg) vector_base as u64,
            options(nostack)
        );
    }
}

#[inline]
fn configure_sctlr_el2() {
    SCTLR_EL2.write(
        SCTLR_EL2::M::Enable
            + SCTLR_EL2::C::Cacheable
            + SCTLR_EL2::I::Cacheable
    );
}

#[inline]
fn configure_timer_el2() {
    // CNTHCTL_EL2: control register for EL2 access to the physical timer and counter registers
    // Bit 0: EL1PCTEN (don't trap EL1 access to the physical counter)
    // Bit 1: EL1PCEN (don't trap EL1 access to the physical timer)
    let cnthctl: u64 = 0x3;
    unsafe {
        core::arch::asm!("msr CNTHCTL_EL2, {}", in(reg) cnthctl);
    }
    
    // CNTVOFF_EL2: virtual timer offset register
    let cntvoff: u64 = 0;
    unsafe {
        core::arch::asm!("msr CNTVOFF_EL2, {}", in(reg) cntvoff);
    }
}

#[inline]
pub fn shutdown_guest() {
    HCR_EL2.write(
        HCR_EL2::RW::EL1AArch64
            + HCR_EL2::SWIO::Set
    );
    unsafe {
        // Disable vGIC CPU interface to restore normal physical IRQ handling
        let mut ich_hcr: u64;
        core::arch::asm!(
            "mrs {tmp}, ich_hcr_el2",
            "bic {tmp}, {tmp}, #1",
            "msr ich_hcr_el2, {tmp}",
            "isb",
            tmp = out(reg) ich_hcr,
            options(nostack)
        );
    }
}

// Hypervisor initialization
#[cfg(virtualization)]
pub fn hyp_init() {
    configure_hcr_el2();
    configure_timer_el2();
    mmu_el2::enable_el2_mmu();
    unsafe {
        core::arch::asm!("dsb sy", options(nostack));
        core::arch::asm!("isb sy", options(nostack));
    }

    let vector_base = vector::get_vector_table_addr();
    configure_vector_table(vector_base);
}

#[cfg(not(virtualization))]
pub fn hyp_init() {
    let hcr_val: u64 = (1 << 31) | (1 << 1);
    write_hcr_el2(hcr_val);

    unsafe {
        core::arch::asm!("dsb sy", options(nostack));
        core::arch::asm!("isb sy", options(nostack));
    }
}