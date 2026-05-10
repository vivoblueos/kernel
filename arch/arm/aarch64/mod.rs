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

#[repr(C, align(16))]
struct TempBootStack([u8; 4096]);

static mut TEMP_BOOT_STACK: TempBootStack = TempBootStack([0u8; 4096]);

unsafe extern "C" {
    pub fn aarch64_boot_entry();
}

pub mod context;
pub mod irq;
pub mod asm;
pub mod mmu;
pub mod psci;
pub mod registers;
pub mod vector;
mod exception;
pub mod virt;

pub use context::{Context, IsrContext, TrapContext};

pub const NR_SWITCH: usize = !0;

#[inline(never)]
pub extern "C" fn svc_switch_context_with_hook(hook: crate::RawContextSwitchHook) {
    // Keep the old AArch64 scheduler switch ABI: x0 carries the opaque
    // scheduler hook and x8 carries NR_SWITCH before trapping through SVC.
    // Exception entry owns the raw frame, while kernel policy remains behind
    // the prepare/finish callbacks.
    unsafe {
        core::arch::asm!(
            "svc #0",
            in("x0") hook as usize,
            in("x8") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline]
pub extern "C" fn switch_context_with_hook(hook: crate::RawContextSwitchHook) {
    svc_switch_context_with_hook(hook)
}

#[inline(always)]
#[allow(clippy::empty_loop)]
pub extern "C" fn restore_context_with_hook(hook: crate::RawContextSwitchHook) -> ! {
    switch_context_with_hook(hook);
    loop {}
}

#[naked]
pub extern "C" fn switch_stack(to_sp: usize, cont: crate::StackSwitchContinuation) -> ! {
    // This is the old signal stack trampoline moved from the kernel facade:
    // switch SP to x0, pass the previous SP as x1, and tail-call the kernel
    // continuation in x1/x19.
    unsafe {
        core::arch::naked_asm!(
            "
            mov x19, x1
            mov x1, sp
            mov sp, x0
            br x19
            "
        )
    }
}

core::arch::global_asm!(
    r#"
.section .text._start, "ax"
.align 11
.global aarch64_boot_entry
.type aarch64_boot_entry, %function
aarch64_boot_entry:
    /* Mask IRQ and FIQ during early boot. */
    msr daifset, #3

    /* Enable floating point and SIMD at EL1. */
    mrs x0, cpacr_el1
    orr x0, x0, #(0x3 << 20)
    msr cpacr_el1, x0
    isb

    /* Allow EL1 access to the physical timer when entering from EL2. */
    mrs x0, cnthctl_el2
    orr x0, x0, #3
    msr cnthctl_el2, x0
    msr cntvoff_el2, xzr

    /*
     * Use the top 4 KiB of each hart's 16 KiB system stack chunk for EL2
     * setup, and reserve the rest as the EL1 stack.
     */
    ldr x1, =__sys_stack_end
    mrs x9, mpidr_el1
    and x9, x9, #0xff
    lsl x9, x9, #14
    sub x1, x1, x9
    mov sp, x1
    mov x19, x1
    sub x2, x1, #0x1000
    msr sp_el1, x2

    /* Configure EL2 state before dropping to EL1. */
    bl aarch64_virt_init

    /* Return to EL1h with interrupts masked. */
    mov x0, #0x3c5
    msr spsr_el2, x0

    /* Enable EL1 MMU while still running in EL2. */
    ldr x4, ={tmp_stack}
    add x4, x4, #0x1000
    mov sp, x4
    bl aarch64_enable_mmu
    mov sp, x19

    /* Enter EL1 and continue with the common kernel boot path. */
    ldr x0, =__sys_stack_start
    ldr x2, =kernel_boot
    adr x3, .Lstartup_el1
    msr elr_el2, x3
    eret

.Lstartup_el1:
    mrs x8, mpidr_el1
    and x8, x8, #0xff
    lsl x8, x8, #14
    sub sp, x1, x8
    br x2

.size aarch64_boot_entry, . - aarch64_boot_entry
"#,
    tmp_stack = sym TEMP_BOOT_STACK,
);
