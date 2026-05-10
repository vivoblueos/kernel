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

unsafe extern "C" {
    pub fn riscv_boot_entry();
}

pub mod context;
pub mod irq;
mod trap;

pub use context::{Context, IsrContext, TrapContext};
pub use trap::trap_entry;

pub const NR_SWITCH: usize = !0;

pub type RawContextSwitcher = extern "C" fn(hook: crate::RawContextSwitchHook, old_sp: usize) -> usize;

pub extern "C" fn ecall_switch_context_with_hook(hook: crate::RawContextSwitchHook) {
    // Keep the old RISC-V scheduler switch ABI: a0 carries the opaque
    // scheduler hook and a7 carries NR_SWITCH. Trap entry owns the register
    // frame; kernel policy is called back later with the raw hook pointer.
    unsafe {
        core::arch::asm!(
            "ecall",
            in("a0") hook as usize,
            in("a7") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline(always)]
pub extern "C" fn switch_context_with_hook(hook: crate::RawContextSwitchHook) {
    ecall_switch_context_with_hook(hook)
}

#[inline(always)]
pub extern "C" fn restore_context_with_hook(hook: crate::RawContextSwitchHook) -> ! {
    switch_context_with_hook(hook);
    unreachable!("Should have switched to another thread");
}

#[naked]
pub extern "C" fn switch_stack(to_sp: usize, cont: crate::StackSwitchContinuation) -> ! {
    // Move to a raw stack and tail-call the kernel continuation. This mirrors
    // the previous kernel facade helper; the old stack pointer is passed as
    // the continuation's second argument.
    unsafe {
        core::arch::naked_asm!(
            "
            mv t0, a1
            mv a1, sp
            mv sp, a0
            jalr x0, t0, 0
            "
        )
    }
}

#[naked]
pub extern "C" fn switch_stack_with_hook(
    hook: crate::RawContextSwitchHook,
    old_sp: usize,
    to_sp: usize,
    ra: usize,
    switcher: RawContextSwitcher,
) -> ! {
    // RISC-V ecall switching used to keep this tiny stack pivot in the kernel
    // callback. It is register ABI, not scheduler policy: a2 is the selected
    // next saved_sp, a3 is the trap continuation return address, and a4 is a
    // kernel callback that consumes the raw hook on the new stack.
    unsafe { core::arch::naked_asm!("mv sp, a2", "mv ra, a3", "jalr x0, a4, 0") }
}

#[cfg(has_mie)]
core::arch::global_asm!(
    r#"
.section .text._start, "ax"
.align 2
.global _start
.global riscv_boot_entry
.type _start, @function
.type riscv_boot_entry, @function
_start:
riscv_boot_entry:
    /* Disable machine interrupts during early boot. */
    csrci mstatus, 0x8

    /* Initialize the global pointer before touching small data. */
    la gp, __global_pointer$

    /* Give each hart a private early stack slot. */
    la sp, __sys_stack_end
    csrr t0, mhartid
    slli t0, t0, 12
    sub sp, sp, t0

    /* Return from traps to machine mode with interrupts enabled later. */
    li t0, 0x1800
    li t1, 0x80
    or t0, t0, t1
    csrs mstatus, t0

    /* Enable machine timer, software, and external interrupt sources. */
    li t0, 0x888
    csrs mie, t0

    /* Continue in the kernel boot code. */
    la t0, kernel_boot
    jalr x0, t0, 0

.size _start, . - _start
.size riscv_boot_entry, . - riscv_boot_entry
"#
);

#[cfg(not(has_mie))]
core::arch::global_asm!(
    r#"
.section .text._start, "ax"
.align 2
.global _start
.global riscv_boot_entry
.type _start, @function
.type riscv_boot_entry, @function
_start:
riscv_boot_entry:
    /* Disable machine interrupts during early boot. */
    csrci mstatus, 0x8

    /* Initialize the global pointer before touching small data. */
    la gp, __global_pointer$

    /* Give each hart a private early stack slot. */
    la sp, __sys_stack_end
    csrr t0, mhartid
    slli t0, t0, 12
    sub sp, sp, t0

    /* Return from traps to machine mode with interrupts enabled later. */
    li t0, 0x1800
    li t1, 0x80
    or t0, t0, t1
    csrs mstatus, t0

    /*
     * Some RISC-V MCUs, such as ESP32-C3, do not implement the standard mie
     * CSR. Their interrupt controller is initialized by board-specific code.
     */

    /* Continue in the kernel boot code. */
    la t0, kernel_boot
    jalr x0, t0, 0

.size _start, . - _start
.size riscv_boot_entry, . - riscv_boot_entry
"#
);
