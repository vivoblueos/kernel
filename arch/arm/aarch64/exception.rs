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

use super::{context::TrapContext, irq};
use crate::{RawExceptionFrame, SyscallRequest};
use core::{
    arch::{asm, naked_asm},
    mem::offset_of,
    sync::atomic::{compiler_fence, Ordering},
};

const NR_SWITCH: usize = !0;
const SVC_AARCH64_EC: usize = 0x15;
const FIQ_DISPATCH: usize = 1;
const IRQ_DISPATCH: usize = 0;

macro_rules! aarch64_save_context_prologue {
    () => {
        "
        sub sp, sp, #{stack_size}
        str lr, [sp, #{lr}]
        "
    };
}

macro_rules! aarch64_restore_context_epilogue {
    () => {
        "
        ldr lr, [sp, #{lr}]
        add sp, sp, #{stack_size}
        "
    };
}

macro_rules! aarch64_save_context {
    () => {
        "
        stp x0, x1, [sp, #{x0}]
        stp x2, x3, [sp, #{x2}]
        stp x4, x5, [sp, #{x4}]
        stp x6, x7, [sp, #{x6}]
        stp x8, x9, [sp, #{x8}]
        stp x10, x11, [sp, #{x10}]
        stp x12, x13, [sp, #{x12}]
        stp x14, x15, [sp, #{x14}]
        stp x16, x17, [sp, #{x16}]
        stp x18, x19, [sp, #{x18}]
        stp x20, x21, [sp, #{x20}]
        stp x22, x23, [sp, #{x22}]
        stp x24, x25, [sp, #{x24}]
        stp x26, x27, [sp, #{x26}]
        stp x28, x29, [sp, #{x28}]
        mrs x8, elr_el1
        str x8, [sp, #{elr}]
        mrs x8, spsr_el1
        str x8, [sp, #{spsr}]
        stp q0, q1, [sp, #{v0}]
        stp q2, q3, [sp, #{v2}]
        stp q4, q5, [sp, #{v4}]
        stp q6, q7, [sp, #{v6}]
        stp q8, q9, [sp, #{v8}]
        stp q10, q11, [sp, #{v10}]
        stp q12, q13, [sp, #{v12}]
        stp q14, q15, [sp, #{v14}]
        stp q16, q17, [sp, #{v16}]
        stp q18, q19, [sp, #{v18}]
        stp q20, q21, [sp, #{v20}]
        stp q22, q23, [sp, #{v22}]
        stp q24, q25, [sp, #{v24}]
        stp q26, q27, [sp, #{v26}]
        stp q28, q29, [sp, #{v28}]
        stp q30, q31, [sp, #{v30}]
        mrs x8, fpcr
        str x8, [sp, #{fpcr}]
        mrs x8, fpsr
        str x8, [sp, #{fpsr}]
        "
    };
}

macro_rules! aarch64_restore_context {
    () => {
        "
        ldr x8, [sp, #{fpcr}]
        msr fpcr, x8
        ldr x8, [sp, #{fpsr}]
        msr fpsr, x8
        ldp q0, q1, [sp, #{v0}]
        ldp q2, q3, [sp, #{v2}]
        ldp q4, q5, [sp, #{v4}]
        ldp q6, q7, [sp, #{v6}]
        ldp q8, q9, [sp, #{v8}]
        ldp q10, q11, [sp, #{v10}]
        ldp q12, q13, [sp, #{v12}]
        ldp q14, q15, [sp, #{v14}]
        ldp q16, q17, [sp, #{v16}]
        ldp q18, q19, [sp, #{v18}]
        ldp q20, q21, [sp, #{v20}]
        ldp q22, q23, [sp, #{v22}]
        ldp q24, q25, [sp, #{v24}]
        ldp q26, q27, [sp, #{v26}]
        ldp q28, q29, [sp, #{v28}]
        ldp q30, q31, [sp, #{v30}]
        ldr x8, [sp, #{spsr}]
        and x9, x8, #~(1 << 7)
        msr spsr_el1, x9
        ldr x8, [sp, #{elr}]
        msr elr_el1, x8
        ldp x0, x1, [sp, #{x0}]
        ldp x2, x3, [sp, #{x2}]
        ldp x4, x5, [sp, #{x4}]
        ldp x6, x7, [sp, #{x6}]
        ldp x8, x9, [sp, #{x8}]
        ldp x10, x11, [sp, #{x10}]
        ldp x12, x13, [sp, #{x12}]
        ldp x14, x15, [sp, #{x14}]
        ldp x16, x17, [sp, #{x16}]
        ldp x18, x19, [sp, #{x18}]
        ldp x20, x21, [sp, #{x20}]
        ldp x22, x23, [sp, #{x22}]
        ldp x24, x25, [sp, #{x24}]
        ldp x26, x27, [sp, #{x26}]
        ldp x28, x29, [sp, #{x28}]
        "
    };
}

macro_rules! exception_handler {
    ($name:ident, $cont:path) => {
        #[no_mangle]
        #[naked]
        unsafe extern "C" fn $name() -> ! {
            naked_asm!(
                concat!(
                    "
                    msr DAIFSet, #0x3
                    ",
                    aarch64_save_context_prologue!(),
                    aarch64_save_context!(),
                    "
                    mov x0, sp
                    bl {cont}
                    mov sp, x0
                    ",
                    aarch64_restore_context!(),
                    aarch64_restore_context_epilogue!(),
                    "
                    eret
                    ",
                ),
                lr = const offset_of!(TrapContext, lr),
                stack_size = const core::mem::size_of::<TrapContext>(),
                x0 = const offset_of!(TrapContext, x0),
                x2 = const offset_of!(TrapContext, x2),
                x4 = const offset_of!(TrapContext, x4),
                x6 = const offset_of!(TrapContext, x6),
                x8 = const offset_of!(TrapContext, x8),
                x10 = const offset_of!(TrapContext, x10),
                x12 = const offset_of!(TrapContext, x12),
                x14 = const offset_of!(TrapContext, x14),
                x16 = const offset_of!(TrapContext, x16),
                x18 = const offset_of!(TrapContext, x18),
                x20 = const offset_of!(TrapContext, x20),
                x22 = const offset_of!(TrapContext, x22),
                x24 = const offset_of!(TrapContext, x24),
                x26 = const offset_of!(TrapContext, x26),
                x28 = const offset_of!(TrapContext, x28),
                spsr = const offset_of!(TrapContext, spsr),
                elr = const offset_of!(TrapContext, elr),
                v0 = const offset_of!(TrapContext, v0),
                v2 = const offset_of!(TrapContext, v2),
                v4 = const offset_of!(TrapContext, v4),
                v6 = const offset_of!(TrapContext, v6),
                v8 = const offset_of!(TrapContext, v8),
                v10 = const offset_of!(TrapContext, v10),
                v12 = const offset_of!(TrapContext, v12),
                v14 = const offset_of!(TrapContext, v14),
                v16 = const offset_of!(TrapContext, v16),
                v18 = const offset_of!(TrapContext, v18),
                v20 = const offset_of!(TrapContext, v20),
                v22 = const offset_of!(TrapContext, v22),
                v24 = const offset_of!(TrapContext, v24),
                v26 = const offset_of!(TrapContext, v26),
                v28 = const offset_of!(TrapContext, v28),
                v30 = const offset_of!(TrapContext, v30),
                fpcr = const offset_of!(TrapContext, fpcr),
                fpsr = const offset_of!(TrapContext, fpsr),
                cont = sym $cont,
            );
        }
    };
}

exception_handler!(el1_fiq, trap_fiq);
exception_handler!(el1_sync, trap_sync);
exception_handler!(el1_irq, trap_irq);
exception_handler!(el1_error, trap_exception);

macro_rules! unsupported_handler {
    ($name:ident, $msg:expr) => {
        #[no_mangle]
        unsafe extern "C" fn $name() {
            panic!($msg);
            asm!("b .");
        }
    };
}

unsupported_handler!(el0_not_supported, "el0 is not supported.");
unsupported_handler!(lowerel_not_supported, "lowerel is not supported.");

#[naked]
unsafe extern "C" fn trap_sync() -> ! {
    naked_asm!(
        "
        mov x19, lr
        mov x20, x0
        bl {handle_svc}
        mov sp, x0
        mov x1, x20
        mov lr, x19
        b {might_switch}
        ",
        handle_svc = sym handle_svc,
        might_switch = sym might_switch,
    );
}

extern "C" fn might_switch(to: RawExceptionFrame, from: RawExceptionFrame) -> usize {
    let from_ctx = unsafe { &*from.cast::<TrapContext>() };
    debug_assert_eq!(to != from, from_ctx.x8 == NR_SWITCH);
    if to == from {
        return from as usize;
    }

    // The old kernel-side might_switch() read ContextSwitchHookHolder from
    // from.x0 and completed scheduler bookkeeping here. That hook type still
    // belongs to the kernel in Phase 3, so this raw callback preserves the
    // behavior without creating a kernel dependency in bluekernel_arch.
    unsafe { crate::blueos_kernel_aarch64_finish_svc_switch(to, from) }
}

extern "C" fn handle_svc(context: &mut TrapContext) -> usize {
    let esr = read_esr_el1();
    let ec = ((esr >> 26) & 0x3f) as usize;
    let old_sp = context as *mut _ as RawExceptionFrame;
    if ec != SVC_AARCH64_EC {
        unsafe { crate::blueos_kernel_fatal_trap(old_sp, ec, esr as usize) };
    }
    if context.x8 == NR_SWITCH {
        // This mirrors the old prepare_for_context_switch() call. The kernel
        // still owns the hook and next-thread selection until Phase 4, so the
        // arch entry only passes the raw Context-compatible frame.
        return unsafe { crate::blueos_kernel_aarch64_prepare_svc_switch(old_sp) };
    }

    compiler_fence(Ordering::SeqCst);
    let sc = SyscallRequest {
        nr: context.x8,
        args: [
            context.x0, context.x1, context.x2, context.x3, context.x4, context.x5,
        ],
    };
    enable_local_irq();
    context.x0 = unsafe { crate::blueos_kernel_dispatch_syscall(&sc) };
    disable_local_irq();
    compiler_fence(Ordering::SeqCst);
    old_sp as usize
}

extern "C" fn trap_exception(context: &mut TrapContext) -> usize {
    let sp = context as *mut _ as RawExceptionFrame;
    let esr = read_esr_el1();
    let ec = ((esr >> 26) & 0x3f) as usize;
    unsafe { crate::blueos_kernel_fatal_trap(sp, ec, esr as usize) };
}

extern "C" fn trap_irq(context: &mut TrapContext) -> usize {
    let sp = context as *mut _ as RawExceptionFrame;
    let irq = irq::get_interrupt();
    let raw = u32::from(irq) as usize;
    unsafe { crate::blueos_kernel_dispatch_external_irq(sp, raw, IRQ_DISPATCH) };
    irq::end_interrupt(irq);
    sp as usize
}

extern "C" fn trap_fiq(context: &mut TrapContext) -> usize {
    let sp = context as *mut _ as RawExceptionFrame;
    let fiq = irq::get_interrupt();
    let raw = u32::from(fiq);
    if raw != irq::SPECIAL_NONE {
        // Keep the old FIQ special-id behavior: ID 1023 means no interrupt
        // was acknowledged, so there is no kernel ISR registry entry to run.
        unsafe { crate::blueos_kernel_dispatch_external_irq(sp, raw as usize, FIQ_DISPATCH) };
    }
    irq::end_interrupt(fiq);
    sp as usize
}

#[inline]
fn read_esr_el1() -> u64 {
    let esr: u64;
    unsafe { asm!("mrs {}, esr_el1", out(reg) esr, options(nostack)) };
    esr
}

#[inline]
fn disable_local_irq() {
    unsafe { asm!("msr daifset, #3", options(nostack, nomem)) }
}

#[inline]
fn enable_local_irq() {
    unsafe { asm!("msr daifclr, #3", options(nostack, nomem)) }
}
