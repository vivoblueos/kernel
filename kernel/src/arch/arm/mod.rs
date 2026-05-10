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

use crate::{
    scheduler,
    support::{sideeffect, Region, RegionalObjectBuilder},
    syscalls::{dispatch_syscall, Context as ScContext},
};
pub(crate) use bluekernel_arch::cortex_m::hardfault::handle_hardfault;
use bluekernel_arch::cortex_m::{asm as cortex_asm, scb};
pub use bluekernel_arch::cortex_m::{
    current_sp, disable_local_irq, disable_local_irq_save, enable_local_irq,
    enable_local_irq_restore, idle, irq, local_irq_enabled, Context, ExceptionStackFrame,
};
#[cfg(use_mpu)]
pub mod mpu;

use core::mem::offset_of;
use scheduler::ContextSwitchHookHolder;

// See https://developer.arm.com/documentation/100235/0100/The-Cortex-M33-Processor/Programmer-s-model/Core-registers/CONTROL-register.
#[cfg(not(target_abi = "eabihf"))]
pub const CONTROL: usize = 0b10;
#[cfg(target_abi = "eabihf")]
pub const CONTROL: usize = 0b110;
pub const THUMB_MODE: usize = bluekernel_arch::cortex_m::THUMB_MODE_XPSR;
pub const NR_SWITCH: usize = !0;
pub const NR_RET_FROM_SYSCALL: usize = NR_SWITCH - 1;
pub const NR_DEBUG_SYSCALL: usize = NR_SWITCH - 2;
pub const DISABLE_LOCAL_IRQ_BASEPRI: u8 = bluekernel_arch::cortex_m::LOCAL_IRQ_BASEPRI as u8;
// Keep one callee-saved register macro: the assembler elides S16-S31 handling
// for non-hard-float builds, matching the ABI-gated fields in `Context`.
#[cfg(target_abi = "eabihf")]
const CALLEE_SAVED_FPU_REGS: usize = 1;
#[cfg(not(target_abi = "eabihf"))]
const CALLEE_SAVED_FPU_REGS: usize = 0;

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn bk_handle_hardfault() {
    handle_hardfault()
}

#[no_mangle]
pub unsafe extern "C" fn handle_systick() {
    if !crate::boards::ClockImpl::claim_interrupt() {
        return;
    }
    crate::time::handle_clock_interrupt();
}

#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:expr, $stack_end:expr, $cont:path) => {
        core::arch::naked_asm!(
            "cpsid i",
            "b {cont}",
            cont = sym $cont,
        )
    };
}

extern "C" fn prepare_schedule() -> usize {
    let current = scheduler::current_thread_ref();
    // Program guard for the first thread before entering thread mode with PSP.
    #[cfg(all(use_mpu, mpu_stack_guard))]
    mpu::update_thread_stack_guard(current);
    current.reset_saved_sp();
    current.saved_sp()
}

extern "C" {
    pub static mut __sys_stack_end: u8;
}

pub extern "C" fn reset_msp_and_start_schedule(msp: *mut u8, cont: extern "C" fn() -> !) {
    let sp = prepare_schedule();
    unsafe {
        // Reset handler entry is special: after switching MSP/PSP, the code
        // must not return or let the compiler use the old stack again. See:
        // https://stackoverflow.com/questions/59008284/if-the-main-function-is-called-inside-the-reset-handler-how-other-interrupts-ar
        cortex_asm::reset_stack_pointers_and_start(
            msp,
            sp,
            THUMB_MODE,
            CONTROL,
            DISABLE_LOCAL_IRQ_BASEPRI as usize,
            cont,
        )
    }
}

#[inline]
pub extern "C" fn start_schedule(cont: extern "C" fn() -> !) {
    #[cfg(use_mpu)]
    mpu::init_sys_stack_guard();
    unsafe { reset_msp_and_start_schedule(&mut __sys_stack_end as *mut u8, cont) }
}

// FIXME: We need to pass a scratch register to perform saving.
// Use r12 as scratch register now.
macro_rules! store_callee_saved_regs {
    () => {
        "
        mrs r12, psp
        .if {callee_saved_fpu_regs}
        vstmdb r12!, {{s16-s31}}
        .endif
        stmdb r12!, {{r4-r11}}
        "
    };
}

macro_rules! load_callee_saved_regs {
    () => {
        "
        ldmia r12!, {{r4-r11}}
        .if {callee_saved_fpu_regs}
        vldmia r12!, {{s16-s31}}
        .endif
        msr psp, r12
        "
    };
}

#[inline(always)]
pub(crate) extern "C" fn post_pendsv() {
    unsafe { scb::set_pendsv() };
    unsafe { cortex_asm::isb() }
}

#[naked]
#[no_mangle]
pub unsafe extern "C" fn handle_svc() {
    core::arch::naked_asm!(
        concat!(
            "
            ldr r12, ={basepri}
            msr basepri, r12
            isb
            ",
            store_callee_saved_regs!(),
            "
            mov r0, r12
            push {{r3, lr}}
            bl {syscall_handler}
            pop {{r3, lr}}
            mov r12, r0
            ",
            load_callee_saved_regs!(),
            "
            ldr r12, =0
            msr basepri, r12
            bx lr
            ",
        ),
        syscall_handler = sym handle_syscall,
        basepri = const DISABLE_LOCAL_IRQ_BASEPRI,
        callee_saved_fpu_regs = const CALLEE_SAVED_FPU_REGS,
    )
}

extern "C" fn syscall_handler(ctx: &mut Context) {
    let sc = ScContext {
        nr: ctx.r7,
        args: [ctx.r0, ctx.r1, ctx.r2, ctx.r3, ctx.r4, ctx.r5],
    };
    // r0 should contain the return value.
    ctx.r0 = dispatch_syscall(&sc);
}

#[naked]
unsafe extern "C" fn syscall_stub(ctx: *mut Context) -> ! {
    core::arch::naked_asm!(
        concat!(
            "
            push {{r0, lr}}
            bl {syscall_handler}
            pop {{r0, lr}}
            ldr r7, ={syscall_ret}
            svc 0
            ",
        ),
        syscall_handler = sym syscall_handler,
        syscall_ret = const NR_RET_FROM_SYSCALL,
    )
}

#[inline(never)]
fn handle_svc_switch(ctx: &Context) -> usize {
    // r0 contains pointer to the saved_sp of the `from` thread, null
    // if saving context is not needed;
    // r1 contains the saved_sp of the `to` thread;
    // r2 contains the pointer to the switch hook holder, null if
    // there is no switch hook holder.
    debug_assert_eq!(ctx.r7, NR_SWITCH);
    let hook_ptr: *mut ContextSwitchHookHolder = unsafe { ctx.r0 as *mut ContextSwitchHookHolder };
    debug_assert!(!hook_ptr.is_null());
    let hook = unsafe { &mut *hook_ptr };
    scheduler::save_context_finish_hook(&mut *hook, ctx as *const _ as usize)
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn bk_debug_syscall(ctx: &Context) -> usize {
    ctx as *const _ as usize
}

extern "C" fn handle_syscall(ctx: &Context) -> usize {
    if ctx.r7 == NR_DEBUG_SYSCALL {
        return bk_debug_syscall(ctx);
    }
    if ctx.r7 == NR_SWITCH {
        return handle_svc_switch(ctx);
    }
    if ctx.r7 == NR_RET_FROM_SYSCALL {
        // We are using syscall(NR_RET_FROM_SYSCALL, ctx_before_syscall) to
        // return from syscall. ctx_before_syscall is contained in r0.
        return ctx.r0;
    }
    // Due to cortex-m's limitation, we split syscall handling into 2 phases:
    // P0:
    //   Switch stack, go back to thread mode and run handler. Then syscalls
    //   NR_RET_FROM_SYSCALL to go back to ISR mode.
    // P1:
    //   Switch stack and return to the normal control flow of thread mode.

    // Duplicate ctx so that we can exit to thread mode to
    // handle syscalls.
    let size = core::mem::size_of::<Context>();
    let base = unsafe { (ctx as *const Context).byte_offset(-(size as isize)) as usize };
    debug_assert_eq!(base % core::mem::align_of::<Context>(), 0);
    let region = Region { base, size };
    let mut rb = RegionalObjectBuilder::new(region);
    let dup_ctx = rb.write_after_start::<Context>(*ctx).unwrap() as *mut Context as *mut usize;
    unsafe {
        sideeffect();
        dup_ctx
            .byte_offset(
                (offset_of!(Context, exception_frame) + offset_of!(ExceptionStackFrame, pc))
                    as isize,
            )
            .write_volatile(syscall_stub as usize);
        dup_ctx
            .byte_offset(
                (offset_of!(Context, exception_frame) + offset_of!(ExceptionStackFrame, r0))
                    as isize,
            )
            .write_volatile(ctx as *const _ as usize);
        dup_ctx
            .byte_offset(
                (offset_of!(Context, exception_frame) + offset_of!(ExceptionStackFrame, xpsr))
                    as isize,
            )
            .write_volatile(ctx.xpsr_without_stack_alignment_padding())
    }
    base
}

#[naked]
#[no_mangle]
pub unsafe extern "C" fn handle_pendsv() {
    core::arch::naked_asm!(
        concat!(
            "
            ldr r12, ={basepri}
            msr basepri, r12
            isb
            ",
            store_callee_saved_regs!(),
            "
            push {{r3, lr}}
            mov r0, r12
            bl {next_thread_sp}
            mov r12, r0
            pop {{r3, lr}}
            ",
            load_callee_saved_regs!(),
            "
            ldr r12, =0
            msr basepri, r12
            bx lr
            "
        ),
        next_thread_sp = sym scheduler::relinquish_me_and_return_next_sp,
        basepri = const DISABLE_LOCAL_IRQ_BASEPRI,
        callee_saved_fpu_regs = const CALLEE_SAVED_FPU_REGS,
    )
}

#[inline(never)]
pub(crate) extern "C" fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    unsafe {
        core::arch::asm!(
            "movs {tmp}, r7",
            "ldr r7, ={nr}",
            "svc 0",
            "mov r7, {tmp}",
            in("r0") hook as usize,
            tmp = out(reg) _,
            nr = const NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline(always)]
pub extern "C" fn pend_switch_context() {
    post_pendsv();
}

#[inline]
pub extern "C" fn current_cpu_id() -> usize {
    0
}

#[naked]
pub(crate) extern "C" fn switch_stack(
    to_sp: usize,
    cont: extern "C" fn(sp: usize, old_sp: usize),
) -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
            mov r12, r1
            mrs r1, psp
            msr psp, r0
            bx r12
            "
        )
    }
}

pub extern "C" fn send_ipi(_id: usize) {}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    // See https://developer.arm.com/documentation/107706/0100/Exceptions-and-interrupts-overview/Stack-frames.
    #[test]
    fn test_abi() {
        #[cfg(target_abi = "eabihf")]
        {
            assert_eq!(
                core::mem::size_of::<ExceptionStackFrame>(),
                core::mem::size_of::<usize>() * 26
            );
            assert_eq!(
                core::mem::size_of::<Context>(),
                core::mem::size_of::<ExceptionStackFrame>() + 8 * 4 + 16 * 4
            );
        }
        #[cfg(not(target_abi = "eabihf"))]
        {
            assert_eq!(
                core::mem::size_of::<ExceptionStackFrame>(),
                core::mem::size_of::<usize>() * 8
            );
            assert_eq!(
                core::mem::size_of::<Context>(),
                core::mem::size_of::<ExceptionStackFrame>() + 8 * 4
            );
        }
    }
}
