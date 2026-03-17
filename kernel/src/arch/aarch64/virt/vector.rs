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

use super::hyper;
use core::arch::asm;

static mut PRINTED_ALIGN: bool = false;
const VECTOR_TABLE_SIZE: usize = 2048;
const SYNC_EXCEPTION_OFFSET: usize = 0x400;

core::arch::global_asm!(
    "
.section .text.hyper_vector_table
.align 11
.global hyper_vector_table
hyper_vector_table:
    // Current EL with SP0
    .align 7
        b sync_current_sp0
    .align 7
        b irq_current
    .align 7
        b fiq_current
    .align 7
        b serror_current

    // Current EL with SPx
    .align 7
        b sync_current_spx
    .align 7
        b irq_current
    .align 7
        b fiq_current
    .align 7
        b serror_current

    // Lower EL using AArch64
    .align 7
        b sync_from_lower_el1
    .align 7
        b irq_from_lower_el1
    .align 7
        b fiq_from_lower_el1
    .align 7
        b serror_from_lower_el1

    // Lower EL using AArch32
    .align 7
        b sync_current_spx   // Should not happen for now
    .align 7
        b irq_current
    .align 7
        b fiq_current
    .align 7
        b serror_current
"
);

extern "C" {
    fn hyper_vector_table();
}

#[inline]
pub fn get_vector_table_addr() -> usize {
    hyper_vector_table as *const () as usize
}

#[naked]
#[no_mangle]
pub unsafe extern "C" fn sync_from_lower_el1() {
    core::arch::naked_asm!(
        "sub sp, sp, #272\n",
        "stp x0, x1, [sp, #0]\n",
        "stp x2, x3, [sp, #16]\n",
        "stp x4, x5, [sp, #32]\n",
        "stp x6, x7, [sp, #48]\n",
        "stp x8, x9, [sp, #64]\n",
        "stp x10, x11, [sp, #80]\n",
        "stp x12, x13, [sp, #96]\n",
        "stp x14, x15, [sp, #112]\n",
        "stp x16, x17, [sp, #128]\n",
        "stp x18, x19, [sp, #144]\n",
        "stp x20, x21, [sp, #160]\n",
        "stp x22, x23, [sp, #176]\n",
        "stp x24, x25, [sp, #192]\n",
        "stp x26, x27, [sp, #208]\n",
        "stp x28, x29, [sp, #224]\n",
        "str x30, [sp, #240]\n",
        "mrs x1, elr_el2\n",
        "mrs x2, spsr_el2\n",
        "mrs x3, sp_el1\n",
        "str x1, [sp, #248]\n",
        "str x2, [sp, #256]\n",
        "str x3, [sp, #264]\n",
        "mov x0, sp\n",
        "bl sync_from_lower_el1_rust\n",
        "cbz x0, 1f\n",
        "ldr x1, [sp, #248]\n",
        "ldr x2, [sp, #256]\n",
        "ldr x3, [sp, #264]\n",
        "msr elr_el2, x1\n",
        "msr spsr_el2, x2\n",
        "msr sp_el1, x3\n",
        "isb\n",
        "ldp x0, x1, [sp, #0]\n",
        "ldp x2, x3, [sp, #16]\n",
        "ldp x4, x5, [sp, #32]\n",
        "ldp x6, x7, [sp, #48]\n",
        "ldp x8, x9, [sp, #64]\n",
        "ldp x10, x11, [sp, #80]\n",
        "ldp x12, x13, [sp, #96]\n",
        "ldp x14, x15, [sp, #112]\n",
        "ldp x16, x17, [sp, #128]\n",
        "ldp x18, x19, [sp, #144]\n",
        "ldp x20, x21, [sp, #160]\n",
        "ldp x22, x23, [sp, #176]\n",
        "ldp x24, x25, [sp, #192]\n",
        "ldp x26, x27, [sp, #208]\n",
        "ldp x28, x29, [sp, #224]\n",
        "ldr x30, [sp, #240]\n",
        "add sp, sp, #272\n",
        "eret\n",
        "1:\n",
        "wfi\n",
        "b 1b\n"
    );
}

#[no_mangle]
pub unsafe extern "C" fn sync_from_lower_el1_rust(frame: *mut u64) -> u64 {
    let esr: u64;
    let elr: u64;
    asm!("mrs {}, esr_el2", out(reg) esr, options(nostack));
    asm!("mrs {}, elr_el2", out(reg) elr, options(nostack));
    let ec = (esr >> 26) & 0x3F;

    // EC = 0x16 (HVC64)
    if ec == 0x16 {
        let func_id = *frame.add(0);

        match func_id {
            0x00 => {
                let el = hyper::get_current_el();
                core::ptr::write_volatile(frame.add(0), 0u64);
            }
            _ => {
                panic!("[EL2] Unknown Host HVC:{} ", func_id);
            }
        }
        return 1; // Resume
    }

    // EC = 0x07 (Access to SIMD/FP)
    if ec == 0x07 {
        asm!("msr cptr_el2, xzr");
        return 1;
    }

    0
}

// Temporary placeholder
const HCR_EL2_VI: u64 = 1 << 7;
const HCR_EL2_VF: u64 = 1 << 6;

/// Solve irq from lower el1.
#[naked]
#[no_mangle]
pub unsafe extern "C" fn irq_from_lower_el1() {
    core::arch::naked_asm!(
        "sub sp, sp, #272\n",
        "stp x0, x1, [sp, #0]\n",
        "stp x2, x3, [sp, #16]\n",
        "stp x4, x5, [sp, #32]\n",
        "stp x6, x7, [sp, #48]\n",
        "stp x8, x9, [sp, #64]\n",
        "stp x10, x11, [sp, #80]\n",
        "stp x12, x13, [sp, #96]\n",
        "stp x14, x15, [sp, #112]\n",
        "stp x16, x17, [sp, #128]\n",
        "stp x18, x19, [sp, #144]\n",
        "stp x20, x21, [sp, #160]\n",
        "stp x22, x23, [sp, #176]\n",
        "stp x24, x25, [sp, #192]\n",
        "stp x26, x27, [sp, #208]\n",
        "stp x28, x29, [sp, #224]\n",
        "str x30, [sp, #240]\n",
        "mrs x1, elr_el2\n",
        "mrs x2, spsr_el2\n",
        "str x1, [sp, #248]\n",
        "str x2, [sp, #256]\n",
        "mov x0, sp\n",
        "mov x19, sp\n",
        "bl hyper_trap_irq\n",
        "mov sp, x19\n",
        "ldr x1, [sp, #248]\n",
        "ldr x2, [sp, #256]\n",
        "msr elr_el2, x1\n",
        "msr spsr_el2, x2\n",
        "ldp x0, x1, [sp, #0]\n",
        "ldp x2, x3, [sp, #16]\n",
        "ldp x4, x5, [sp, #32]\n",
        "ldp x6, x7, [sp, #48]\n",
        "ldp x8, x9, [sp, #64]\n",
        "ldp x10, x11, [sp, #80]\n",
        "ldp x12, x13, [sp, #96]\n",
        "ldp x14, x15, [sp, #112]\n",
        "ldp x16, x17, [sp, #128]\n",
        "ldp x18, x19, [sp, #144]\n",
        "ldp x20, x21, [sp, #160]\n",
        "ldp x22, x23, [sp, #176]\n",
        "ldp x24, x25, [sp, #192]\n",
        "ldp x26, x27, [sp, #208]\n",
        "ldp x28, x29, [sp, #224]\n",
        "ldr x30, [sp, #240]\n",
        "add sp, sp, #272\n",
        "eret\n",
    );
}

/// Solve fiq from lower el1.
#[naked]
#[no_mangle]
pub unsafe extern "C" fn fiq_from_lower_el1() {
    core::arch::naked_asm!(
        "sub sp, sp, #272\n",
        "stp x0, x1, [sp, #0]\n",
        "stp x2, x3, [sp, #16]\n",
        "stp x4, x5, [sp, #32]\n",
        "stp x6, x7, [sp, #48]\n",
        "stp x8, x9, [sp, #64]\n",
        "stp x10, x11, [sp, #80]\n",
        "stp x12, x13, [sp, #96]\n",
        "stp x14, x15, [sp, #112]\n",
        "stp x16, x17, [sp, #128]\n",
        "stp x18, x19, [sp, #144]\n",
        "stp x20, x21, [sp, #160]\n",
        "stp x22, x23, [sp, #176]\n",
        "stp x24, x25, [sp, #192]\n",
        "stp x26, x27, [sp, #208]\n",
        "stp x28, x29, [sp, #224]\n",
        "str x30, [sp, #240]\n",
        "mrs x1, elr_el2\n",
        "mrs x2, spsr_el2\n",
        "str x1, [sp, #248]\n",
        "str x2, [sp, #256]\n",
        "mov x0, sp\n",
        "bl hyper_trap_fiq\n",
        "ldr x1, [sp, #248]\n",
        "msr elr_el2, x1\n",
        "ldp x0, x1, [sp, #0]\n",
        "ldp x2, x3, [sp, #16]\n",
        "ldp x4, x5, [sp, #32]\n",
        "ldp x6, x7, [sp, #48]\n",
        "ldp x8, x9, [sp, #64]\n",
        "ldp x10, x11, [sp, #80]\n",
        "ldp x12, x13, [sp, #96]\n",
        "ldp x14, x15, [sp, #112]\n",
        "ldp x16, x17, [sp, #128]\n",
        "ldp x18, x19, [sp, #144]\n",
        "ldp x20, x21, [sp, #160]\n",
        "ldp x22, x23, [sp, #176]\n",
        "ldp x24, x25, [sp, #192]\n",
        "ldp x26, x27, [sp, #208]\n",
        "ldp x28, x29, [sp, #224]\n",
        "ldr x30, [sp, #240]\n",
        "add sp, sp, #272\n",
        "eret\n",
    );
}

/// Solve serror from lower el1.
#[no_mangle]
pub unsafe extern "C" fn serror_from_lower_el1() {
    asm!("eret", options(noreturn));
}

/// Solve sync exception from lower el2 sp0.
#[no_mangle]
pub unsafe extern "C" fn sync_current_sp0() {
    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn sync_current_spx() {
    let esr: u64;
    let elr: u64;
    let far: u64;
    asm!("mrs {}, esr_el2", out(reg) esr, options(nostack));
    asm!("mrs {}, elr_el2", out(reg) elr, options(nostack));
    asm!("mrs {}, far_el2", out(reg) far, options(nostack));

    // Attempt to decode syndrome
    let ec = (esr >> 26) & 0x3F;

    // Data Abort from same EL
    if ec == 0x25 {
        panic!("[EL2] Data Abort (EL2)");
    }

    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn sync_current_el1() {
    let esr: u64;
    let elr: u64;
    let far: u64;
    let spsr: u64;
    asm!("mrs {}, esr_el2", out(reg) esr, options(nostack));
    asm!("mrs {}, elr_el2", out(reg) elr, options(nostack));
    asm!("mrs {}, far_el2", out(reg) far, options(nostack));
    asm!("mrs {}, spsr_el2", out(reg) spsr, options(nostack));
    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn sync_current_el0() {
    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn irq_current() {
    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn fiq_current() {
    loop {
        asm!("wfi");
    }
}

#[no_mangle]
pub unsafe extern "C" fn serror_current() {
    loop {
        asm!("wfi");
    }
}
