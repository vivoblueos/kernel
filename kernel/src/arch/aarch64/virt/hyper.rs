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
    registers::{hcr_el2::HCR_EL2, sctlr_el2::SCTLR_EL2, spsr_el2::SPSR_EL2},
    virt::{guest, mmu_el2, vector, vgic},
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
    super::mmu_s2::init_stage2(guest::LINUX_KERNEL_LOAD_ADDR, guest::LINUX_RAM_SIZE);
    HCR_EL2.write(
        HCR_EL2::VM::Enable
            + HCR_EL2::RW::EL1AArch64
            + HCR_EL2::IMO::EL2Handled
            + HCR_EL2::FMO::EL2Handled
            + HCR_EL2::AMO::EL2Handled
            + HCR_EL2::TSC::Trap,
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
    SCTLR_EL2.write(SCTLR_EL2::M::Enable + SCTLR_EL2::C::Cacheable + SCTLR_EL2::I::Cacheable);
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
unsafe fn deactivate_irq(intid: u64) {
    core::arch::asm!("msr ICC_DIR_EL1, {}", in(reg) intid, options(nostack));
}

#[inline]
pub fn shutdown_guest() {
    HCR_EL2.write(HCR_EL2::RW::EL1AArch64 + HCR_EL2::SWIO::Set);
    unsafe {
        // Disable vGIC CPU interface
        let mut ich_hcr: u64;
        core::arch::asm!(
            "mrs {tmp}, ich_hcr_el2",
            "bic {tmp}, {tmp}, #1",
            "msr ich_hcr_el2, {tmp}",
            "isb",
            tmp = out(reg) ich_hcr,
            options(nostack)
        );

        // Clear all List Registers to invalidate pending/active virtual interrupts
        vgic::clear_all_lrs();

        // Immediately restore EOImode=0 so EOI both drops priority AND deactivates.
        let mut ctlr: u64;
        core::arch::asm!(
            "mrs {tmp2}, ICC_CTLR_EL1",
            "bic {tmp2}, {tmp2}, #2",
            "msr ICC_CTLR_EL1, {tmp2}",
            "isb",
            tmp2 = out(reg) ctlr,
            options(nostack)
        );

        // Deactivate all PPIs (0-31) and UART SPI (33).
        // DIR on an Inactive interrupt is a safe no-op per GICv3 spec.
        // This clears any Active state left by the Guest, allowing
        // running priority to drop to idle so PMR=0xFF takes full effect.
        for intid in 0..32 {
            deactivate_irq(intid as u64);
        }
        deactivate_irq(33);

        let rpr: u64;
        core::arch::asm!("mrs {}, ICC_RPR_EL1", out(reg) rpr, options(nostack));

        // Re-enable Host physical timer (Guest may have disabled CNTP_CTL_EL0).
        // Enable=1, IMASK=0 so IRQ 30 fires for Host scheduler.
        let cntp_ctl: u64 = 1;
        core::arch::asm!("msr CNTP_CTL_EL0, {}", in(reg) cntp_ctl, options(nostack));
        core::arch::asm!("isb", options(nostack));
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
