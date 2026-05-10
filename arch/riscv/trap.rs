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

use super::{
    context::{IsrContext, TrapContext},
    NR_SWITCH,
};
use crate::{RawExceptionFrame, SyscallRequest};
use core::{
    mem::offset_of,
    sync::atomic::{compiler_fence, Ordering},
};

const MSTATUS_MIE: usize = 1 << 3;
const INTERRUPT_MASK: usize = 1usize << (usize::BITS - 1);
const TIMER_INT: usize = INTERRUPT_MASK | 0x7;
const EXTERN_INT: usize = INTERRUPT_MASK | 0xB;
const ECALL: usize = 0xB;
const MSI: usize = INTERRUPT_MASK | 0x3;

#[derive(Default, Debug)]
struct SyscallGuard {
    isr_ctx: IsrContext,
}

#[cfg(target_pointer_width = "64")]
macro_rules! rv_save_context_prologue {
    () => {
        "
        addi sp, sp, -{stack_size}
        sd ra, {ra}(sp)
        "
    };
}

#[cfg(target_pointer_width = "32")]
macro_rules! rv_save_context_prologue {
    () => {
        "
        addi sp, sp, -{stack_size}
        sw ra, {ra}(sp)
        "
    };
}

#[cfg(target_pointer_width = "64")]
macro_rules! rv_restore_context_epilogue {
    () => {
        "
        ld ra, {ra}(sp)
        addi sp, sp, {stack_size}
        "
    };
}

#[cfg(target_pointer_width = "32")]
macro_rules! rv_restore_context_epilogue {
    () => {
        "
        lw ra, {ra}(sp)
        addi sp, sp, {stack_size}
        "
    };
}

#[cfg(target_pointer_width = "64")]
macro_rules! rv_restore_context {
    () => {
        "
        ld t0, {mepc}(sp)
        csrw  mepc, t0
        ld gp, {gp}(sp)
        ld tp, {tp}(sp)
        ld t0, {t0}(sp)
        ld t1, {t1}(sp)
        ld t2, {t2}(sp)
        ld t3, {t3}(sp)
        ld t4, {t4}(sp)
        ld t5, {t5}(sp)
        ld t6, {t6}(sp)
        ld a0, {a0}(sp)
        ld a1, {a1}(sp)
        ld a2, {a2}(sp)
        ld a3, {a3}(sp)
        ld a4, {a4}(sp)
        ld a5, {a5}(sp)
        ld a6, {a6}(sp)
        ld a7, {a7}(sp)
        ld fp, {fp}(sp)
        ld s1, {s1}(sp)
        ld s2, {s2}(sp)
        ld s3, {s3}(sp)
        ld s4, {s4}(sp)
        ld s5, {s5}(sp)
        ld s6, {s6}(sp)
        ld s7, {s7}(sp)
        ld s8, {s8}(sp)
        ld s9, {s9}(sp)
        ld s10, {s10}(sp)
        ld s11, {s11}(sp)
        "
    };
}

#[cfg(target_pointer_width = "32")]
macro_rules! rv_restore_context {
    () => {
        "
        lw t0, {mepc}(sp)
        csrw  mepc, t0
        lw gp, {gp}(sp)
        lw tp, {tp}(sp)
        lw t0, {t0}(sp)
        lw t1, {t1}(sp)
        lw t2, {t2}(sp)
        lw t3, {t3}(sp)
        lw t4, {t4}(sp)
        lw t5, {t5}(sp)
        lw t6, {t6}(sp)
        lw a0, {a0}(sp)
        lw a1, {a1}(sp)
        lw a2, {a2}(sp)
        lw a3, {a3}(sp)
        lw a4, {a4}(sp)
        lw a5, {a5}(sp)
        lw a6, {a6}(sp)
        lw a7, {a7}(sp)
        lw fp, {fp}(sp)
        lw s1, {s1}(sp)
        lw s2, {s2}(sp)
        lw s3, {s3}(sp)
        lw s4, {s4}(sp)
        lw s5, {s5}(sp)
        lw s6, {s6}(sp)
        lw s7, {s7}(sp)
        lw s8, {s8}(sp)
        lw s9, {s9}(sp)
        lw s10, {s10}(sp)
        lw s11, {s11}(sp)
        "
    };
}

#[cfg(target_pointer_width = "64")]
macro_rules! rv_save_context {
    () => {
        "
        sd gp, {gp}(sp)
        sd tp, {tp}(sp)
        sd t0, {t0}(sp)
        sd t1, {t1}(sp)
        sd t2, {t2}(sp)
        sd t3, {t3}(sp)
        sd t4, {t4}(sp)
        sd t5, {t5}(sp)
        sd t6, {t6}(sp)
        sd a0, {a0}(sp)
        sd a1, {a1}(sp)
        sd a2, {a2}(sp)
        sd a3, {a3}(sp)
        sd a4, {a4}(sp)
        sd a5, {a5}(sp)
        sd a6, {a6}(sp)
        sd a7, {a7}(sp)
        sd fp, {fp}(sp)
        sd s1, {s1}(sp)
        sd s2, {s2}(sp)
        sd s3, {s3}(sp)
        sd s4, {s4}(sp)
        sd s5, {s5}(sp)
        sd s6, {s6}(sp)
        sd s7, {s7}(sp)
        sd s8, {s8}(sp)
        sd s9, {s9}(sp)
        sd s10, {s10}(sp)
        sd s11, {s11}(sp)
        csrr t0, mepc
        sd t0, {mepc}(sp)
        "
    };
}

#[cfg(target_pointer_width = "32")]
macro_rules! rv_save_context {
    () => {
        "
        sw gp, {gp}(sp)
        sw tp, {tp}(sp)
        sw t0, {t0}(sp)
        sw t1, {t1}(sp)
        sw t2, {t2}(sp)
        sw t3, {t3}(sp)
        sw t4, {t4}(sp)
        sw t5, {t5}(sp)
        sw t6, {t6}(sp)
        sw a0, {a0}(sp)
        sw a1, {a1}(sp)
        sw a2, {a2}(sp)
        sw a3, {a3}(sp)
        sw a4, {a4}(sp)
        sw a5, {a5}(sp)
        sw a6, {a6}(sp)
        sw a7, {a7}(sp)
        sw fp, {fp}(sp)
        sw s1, {s1}(sp)
        sw s2, {s2}(sp)
        sw s3, {s3}(sp)
        sw s4, {s4}(sp)
        sw s5, {s5}(sp)
        sw s6, {s6}(sp)
        sw s7, {s7}(sp)
        sw s8, {s8}(sp)
        sw s9, {s9}(sp)
        sw s10, {s10}(sp)
        sw s11, {s11}(sp)
        csrr t0, mepc
        sw t0, {mepc}(sp)
        "
    };
}

macro_rules! clear_mstatus_mie {
    () => {
        "
        csrci mstatus, 0x8
        "
    };
}

macro_rules! set_mstatus_mie {
    () => {
        "
        csrsi mstatus, 0x8
        "
    };
}

#[repr(align(4))]
#[link_section = ".trap.handler"]
#[naked]
pub unsafe extern "C" fn trap_entry() {
    // This is the original kernel-side trap entry moved verbatim in shape:
    // save the interrupted Context-compatible frame, enter kernel IRQ
    // accounting, dispatch the trap, then restore the returned stack pointer.
    // The policy calls are now C ABI callbacks so bluekernel_arch stays free of
    // scheduler, syscall, and board dependencies.
    core::arch::naked_asm!(
        concat!(
            rv_save_context_prologue!(),
            rv_save_context!(),
            "
            mv s1, sp
            csrr s2, mcause
            csrr s3, mtval
            call {enter_irq}
            mv a0, s1
            mv a1, s2
            mv a2, s3
            auipc a3, 0
            // Get the address after calling handle_trap. The scheduler switch
            // helper uses it as the return address when the interrupted stack
            // is replaced by another thread's saved stack.
            addi a3, a3, 14
            call {handle_trap}
            mv sp, a0
            call {leave_irq}
            ",
            rv_restore_context!(),
            rv_restore_context_epilogue!(),
            "
            mret
            "
        ),
        enter_irq = sym crate::blueos_kernel_enter_irq,
        leave_irq = sym crate::blueos_kernel_leave_irq,
        handle_trap = sym handle_trap,
        ra = const offset_of!(TrapContext, ra),
        stack_size = const core::mem::size_of::<TrapContext>(),
        gp = const offset_of!(TrapContext, gp),
        tp = const offset_of!(TrapContext, tp),
        t0 = const offset_of!(TrapContext, t0),
        t1 = const offset_of!(TrapContext, t1),
        t2 = const offset_of!(TrapContext, t2),
        t3 = const offset_of!(TrapContext, t3),
        t4 = const offset_of!(TrapContext, t4),
        t5 = const offset_of!(TrapContext, t5),
        t6 = const offset_of!(TrapContext, t6),
        a0 = const offset_of!(TrapContext, a0),
        a1 = const offset_of!(TrapContext, a1),
        a2 = const offset_of!(TrapContext, a2),
        a3 = const offset_of!(TrapContext, a3),
        a4 = const offset_of!(TrapContext, a4),
        a5 = const offset_of!(TrapContext, a5),
        a6 = const offset_of!(TrapContext, a6),
        a7 = const offset_of!(TrapContext, a7),
        fp = const offset_of!(TrapContext, fp),
        s1 = const offset_of!(TrapContext, s1),
        s2 = const offset_of!(TrapContext, s2),
        s3 = const offset_of!(TrapContext, s3),
        s4 = const offset_of!(TrapContext, s4),
        s5 = const offset_of!(TrapContext, s5),
        s6 = const offset_of!(TrapContext, s6),
        s7 = const offset_of!(TrapContext, s7),
        s8 = const offset_of!(TrapContext, s8),
        s9 = const offset_of!(TrapContext, s9),
        s10 = const offset_of!(TrapContext, s10),
        s11 = const offset_of!(TrapContext, s11),
        mepc = const offset_of!(TrapContext, mepc),
    )
}

impl SyscallGuard {
    fn new() -> Self {
        let mut g = Self::default();
        unsafe {
            core::arch::asm!(
                "fence rw, rw",
                "csrr {mstatus}, mstatus",
                "csrr {mcause}, mcause",
                "csrr {mtval}, mtval",
                "csrr {mepc}, mepc",
                mstatus = out(reg) g.isr_ctx.mstatus,
                mcause = out(reg) g.isr_ctx.mcause,
                mtval = out(reg) g.isr_ctx.mtval,
                mepc = out(reg) g.isr_ctx.mepc,
            )
        }
        compiler_fence(Ordering::SeqCst);
        // Match the old RISC-V syscall path: syscalls run outside IRQ
        // accounting with local interrupts re-enabled, then Drop restores the
        // saved trap CSRs and re-enters IRQ accounting before mret.
        unsafe { crate::blueos_kernel_leave_irq() };
        enable_local_irq();
        g
    }
}

impl Drop for SyscallGuard {
    fn drop(&mut self) {
        disable_local_irq();
        unsafe { crate::blueos_kernel_enter_irq() };
        compiler_fence(Ordering::SeqCst);
        unsafe {
            core::arch::asm!(
                "csrw mstatus, {mstatus}",
                "csrw mcause, {mcause}",
                "csrw mtval, {mtval}",
                "csrw mepc, {mepc}",
                mstatus = in(reg) self.isr_ctx.mstatus,
                mcause = in(reg) self.isr_ctx.mcause,
                mtval = in(reg) self.isr_ctx.mtval,
                mepc = in(reg) self.isr_ctx.mepc,
            )
        }
    }
}

#[inline]
fn disable_local_irq() {
    compiler_fence(Ordering::SeqCst);
    unsafe { core::arch::asm!(clear_mstatus_mie!(), options(nostack)) };
}

#[inline]
fn enable_local_irq() {
    unsafe { core::arch::asm!(set_mstatus_mie!(), options(nostack)) };
    compiler_fence(Ordering::SeqCst);
}

#[inline]
fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!("csrr {}, mstatus", out(reg) x,
                         options(nostack))
    };
    x & MSTATUS_MIE != 0
}

#[inline(always)]
fn current_cpu_id() -> usize {
    let id: usize;
    unsafe {
        core::arch::asm!("csrr {}, mhartid", out(reg) id,
                              options(nostack))
    };
    id
}

#[inline(never)]
extern "C" fn handle_ecall(ctx: &mut TrapContext, cont: usize) -> usize {
    let sp = ctx as *const _ as usize;
    ctx.mepc += 4;
    if ctx.a7 == NR_SWITCH {
        // The original kernel implementation handled NR_SWITCH directly here
        // because it could see ContextSwitchHookHolder. Phase 3 keeps that
        // scheduler-owned type in the kernel facade, so the arch crate passes
        // the raw frame and continuation back through a dedicated callback.
        return unsafe {
            crate::blueos_kernel_riscv_handle_ecall_switch(
                ctx as *mut _ as RawExceptionFrame,
                cont,
            )
        };
    }
    {
        compiler_fence(Ordering::SeqCst);
        let _scg = SyscallGuard::new();
        let sc = SyscallRequest {
            nr: ctx.a7,
            args: [ctx.a0, ctx.a1, ctx.a2, ctx.a3, ctx.a4, ctx.a5],
        };
        ctx.a0 = unsafe { crate::blueos_kernel_dispatch_syscall(&sc) };
        compiler_fence(Ordering::SeqCst);
    }
    sp
}

#[inline]
fn might_switch_context(ctx: &mut TrapContext, cont: usize) -> usize {
    // Context-switch policy still belongs to the kernel. This callback is the
    // old might_switch_context() body, moved behind the raw frame ABI until
    // Phase 4 moves the Context owner and switch helpers.
    unsafe {
        crate::blueos_kernel_riscv_might_switch_context(ctx as *mut _ as RawExceptionFrame, cont)
    }
}

extern "C" fn handle_trap(
    ctx: &mut TrapContext,
    mcause: usize,
    mtval: usize,
    cont: usize,
) -> usize {
    debug_assert!(!local_irq_enabled());
    let sp = ctx as *const _ as usize;
    match mcause & (INTERRUPT_MASK | 0x3f) {
        #[cfg(has_plic)]
        EXTERN_INT => {
            // Preserve the original board-owned PLIC dispatch; only the trap
            // entry and top-level cause routing moved into bluekernel_arch.
            unsafe {
                crate::blueos_kernel_dispatch_external_irq(
                    ctx as *mut _ as RawExceptionFrame,
                    mcause,
                    mtval,
                );
            }
            might_switch_context(ctx, cont)
        }
        #[cfg(has_mtime)]
        TIMER_INT => {
            // Timer policy is still kernel-owned. The callback eventually
            // reaches time::handle_clock_interrupt(), matching the old path.
            unsafe { crate::blueos_kernel_handle_timer_tick() };
            might_switch_context(ctx, cont)
        }
        ECALL => handle_ecall(ctx, cont),
        MSI => {
            // Software interrupts are used as WFI/IPI wakeups. Clearing the
            // board-specific source remains behind a kernel callback.
            unsafe { crate::blueos_kernel_clear_software_irq(current_cpu_id()) };
            sp
        }
        #[cfg(not(has_plic))]
        _ if mcause & INTERRUPT_MASK != 0 => {
            // Non-PLIC MCUs such as ESP32-C3 keep their INTC dispatch policy
            // in board code, just as the pre-migration trap handler did.
            unsafe {
                crate::blueos_kernel_dispatch_external_irq(
                    ctx as *mut _ as RawExceptionFrame,
                    mcause,
                    mtval,
                );
            }
            might_switch_context(ctx, cont)
        }
        _ => unsafe {
            crate::blueos_kernel_fatal_trap(ctx as *mut _ as RawExceptionFrame, mcause, mtval)
        },
    }
}
