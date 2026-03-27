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

use crate::arch::aarch64::{registers::hcr_el2::HCR_EL2, virt::vector};
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
fn configure_vector_table(vector_base: usize) {
    unsafe {
        core::arch::asm!(
            "msr vbar_el2, {}",
            in(reg) vector_base as u64,
            options(nostack)
        );
    }
}

// Hypervisor initialization
#[cfg(virtualization)]
pub fn hyp_init() {
    configure_hcr_el2();
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
