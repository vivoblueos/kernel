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

use super::{
    VCPU_MANAGER,
    guest,
    hyper,
    vcpu::Vcpu,
    vgic,
    exit::{
        handle_vm_exit, is_guest_shutdown, clear_guest_shutdown
    }
};
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
        "cbz x0, 3f\n",
        // x0 == 2, Guest shutdown, return to Host.
        "cmp x0, #2\n",
        "b.eq 2f\n",
        // x0 == 1, continue running Guest.
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
        "2:\n",
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
        "3:\n",
        "wfi\n",
        "b 3b\n"
    );
}

#[no_mangle]
pub unsafe extern "C" fn sync_from_lower_el1_rust(frame: *mut u64) -> u64 {
   if let Some(vcpu_id) = VCPU_MANAGER.0.current_vcpu_id() {
        handle_guest_request(vcpu_id, frame)
    } else {
        handle_host_request(frame)
    }
}

unsafe fn handle_guest_request(vcpu_id: usize, frame: *mut u64) -> u64 {
    let vcpu = VCPU_MANAGER.0.get_vcpu(vcpu_id).unwrap();
    save_frame_to_context(frame, vcpu);
    let ok = handle_vm_exit(vcpu);

    if !ok && is_guest_shutdown() {
        core::arch::asm!("msr daifset, #15");
        clear_guest_shutdown();
        hyper::shutdown_guest();
        VCPU_MANAGER.0.clear_current_vcpu();
        restore_host_to_frame(frame);
        2 
    } else {
        restore_context_to_frame(vcpu, frame);
        vgic::flush(vcpu_id);
        1 
    }
}

unsafe fn handle_host_request(frame: *mut u64) -> u64 {
    let func_id = *frame.add(0);
    
    match func_id {
        0x02 => {
            let target_id = *frame.add(1) as usize;
            if let Some(vcpu) = VCPU_MANAGER.0.get_vcpu(target_id) {
                save_host_context(frame); 
                hyper::configure_hcr_el2_for_guest();
                vcpu.prepare_run();
                VCPU_MANAGER.0.set_current_vcpu(target_id);
                restore_context_to_frame(vcpu, frame);
                1 
            } else {
                *frame.add(0) = 1;
                1
            }
        }
        _ => {
            *frame.add(0) = 0; 
            1 
        }
    }
}

unsafe fn save_host_context(frame: *mut u64) {
    VCPU_MANAGER.0.host_elr = *frame.add(31) + 4;
    VCPU_MANAGER.0.host_spsr = *frame.add(32);
    VCPU_MANAGER.0.host_sp = *frame.add(33);
    for i in 0..31 { 
        VCPU_MANAGER.0.host_regs[i] = *frame.add(i);
    }

    let (vbar, sctlr, ttbr0, ttbr1, tcr, mair): (u64, u64, u64, u64, u64, u64);
    core::arch::asm!(
        "mrs {vbar}, vbar_el1",
        "mrs {sctlr}, sctlr_el1",
        "mrs {ttbr0}, ttbr0_el1",
        "mrs {ttbr1}, ttbr1_el1",
        "mrs {tcr}, tcr_el1",
        "mrs {mair}, mair_el1",
        vbar = out(reg) vbar,
        sctlr = out(reg) sctlr,
        ttbr0 = out(reg) ttbr0,
        ttbr1 = out(reg) ttbr1,
        tcr = out(reg) tcr,
        mair = out(reg) mair,
        options(nostack, nomem)
    );
    VCPU_MANAGER.0.host_vbar = vbar;
    VCPU_MANAGER.0.host_sctlr = sctlr;
    VCPU_MANAGER.0.host_ttbr0 = ttbr0;
    VCPU_MANAGER.0.host_ttbr1 = ttbr1;
    VCPU_MANAGER.0.host_tcr = tcr;
    VCPU_MANAGER.0.host_mair = mair;
}

unsafe fn restore_host_to_frame(frame: *mut u64) {
    *frame.add(31) = VCPU_MANAGER.0.host_elr;
    *frame.add(32) = VCPU_MANAGER.0.host_spsr;
    *frame.add(33) = VCPU_MANAGER.0.host_sp;
    // Restore Host GPRs (x0-x30)
    for i in 0..31 {
        *frame.add(i) = VCPU_MANAGER.0.host_regs[i];
    }
    
    // Pass success code (0) back to host's x0
    *frame.add(0) = 0;

    let vbar = VCPU_MANAGER.0.host_vbar;
    let sctlr = VCPU_MANAGER.0.host_sctlr;
    let ttbr0 = VCPU_MANAGER.0.host_ttbr0;
    let ttbr1 = VCPU_MANAGER.0.host_ttbr1;
    let tcr = VCPU_MANAGER.0.host_tcr;
    let mair = VCPU_MANAGER.0.host_mair;

    core::arch::asm!(
        "msr vbar_el1, {vbar}",
        "msr sctlr_el1, {sctlr}",
        "msr ttbr0_el1, {ttbr0}",
        "msr ttbr1_el1, {ttbr1}",
        "msr tcr_el1, {tcr}",
        "msr mair_el1, {mair}",
        "isb",
        "tlbi alle1",
        "dsb sy", 
        "isb",
        vbar = in(reg) vbar,
        sctlr = in(reg) sctlr,
        ttbr0 = in(reg) ttbr0,
        ttbr1 = in(reg) ttbr1,
        tcr = in(reg) tcr,
        mair = in(reg) mair,
    );
}

unsafe fn save_frame_to_context(frame: *mut u64, vcpu: &mut Vcpu) {
    let mut ctx = vcpu.context_mut();
    for i in 0..31 {
        ctx.regs[i] = *frame.add(i);
    }
    ctx.elr_el2 = *frame.add(31);
    ctx.spsr = *frame.add(32);
    ctx.sp = *frame.add(33);
    let (sctlr, ttbr0, ttbr1, tcr, mair, vbar): (u64, u64, u64, u64, u64, u64);
    core::arch::asm!(
        "mrs {sctlr}, sctlr_el1",
        "mrs {ttbr0}, ttbr0_el1",
        "mrs {ttbr1}, ttbr1_el1",
        "mrs {tcr}, tcr_el1",
        "mrs {mair}, mair_el1",
        "mrs {vbar}, vbar_el1",
        sctlr = out(reg) sctlr,
        ttbr0 = out(reg) ttbr0,
        ttbr1 = out(reg) ttbr1,
        tcr   = out(reg) tcr,
        mair  = out(reg) mair,
        vbar  = out(reg) vbar,
        options(nostack, nomem)
    );

    ctx.sctlr_el1 = sctlr;
    ctx.ttbr0_el1 = ttbr0;
    ctx.ttbr1_el1 = ttbr1;
    ctx.tcr_el1   = tcr;
    ctx.mair_el1  = mair;
    ctx.vbar_el1  = vbar; 
}

unsafe fn restore_context_to_frame(vcpu: &mut Vcpu, frame: *mut u64) {
    let ctx = vcpu.context();
    for i in 0..31 { *frame.add(i) = ctx.regs[i]; }
    *frame.add(31) = ctx.elr_el2;
    *frame.add(32) = ctx.spsr;
    *frame.add(33) = ctx.sp;

    // while booting linux, mmu should closed.
    core::arch::asm!(
        "msr vbar_el1, {vbar}",
        "msr ttbr0_el1, {ttbr0}", 
        "msr ttbr1_el1, {ttbr1}",
        "msr tcr_el1, {tcr}",
        "msr mair_el1, {mair}",
        "msr sctlr_el1, {sctlr}", 
        "isb",
        vbar  = in(reg) ctx.vbar_el1,
        ttbr0 = in(reg) ctx.ttbr0_el1,
        ttbr1 = in(reg) ctx.ttbr1_el1,
        tcr   = in(reg) ctx.tcr_el1,
        mair  = in(reg) ctx.mair_el1,
        sctlr = in(reg) ctx.sctlr_el1,
        options(nostack)
    );
    
    let target_vcpu_id = vcpu.id();
    vgic::flush(target_vcpu_id);
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
        "mrs x3, sp_el1\n",
        "str x1, [sp, #248]\n",
        "str x2, [sp, #256]\n",
        "str x3, [sp, #264]\n",
        "mov x0, sp\n",
        "bl hyper_trap_irq\n",
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
