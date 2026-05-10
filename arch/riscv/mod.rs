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

pub mod irq;
mod trap;

pub use trap::{trap_entry, TrapContext};

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
