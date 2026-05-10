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

pub(crate) mod hardfault;
pub(crate) mod xpsr;
use crate::{
    arch::irq,
    scheduler,
    support::{sideeffect, Region, RegionalObjectBuilder},
};
pub(crate) use hardfault::handle_hardfault;
pub use hardfault::panic_on_hardfault;
#[cfg(use_mpu)]
pub mod mpu;

use core::{
    mem::offset_of,
    sync::{atomic, atomic::Ordering},
};
use cortex_m::peripheral::SCB;
use scheduler::ContextSwitchHookHolder;

pub use bluekernel_arch::cortex_m::context::{Context, IsrContext, THUMB_MODE};
pub use bluekernel_arch::cortex_m::{
    restore_context_with_hook, switch_context_with_hook, switch_stack,
};

pub const EXCEPTION_LR: usize = 0xFFFFFFFD;
// See https://developer.arm.com/documentation/100235/0100/The-Cortex-M33-Processor/Programmer-s-model/Core-registers/CONTROL-register.
#[cfg(not(target_abi = "eabihf"))]
pub const CONTROL: usize = 0b10;
#[cfg(target_abi = "eabihf")]
pub const CONTROL: usize = 0b110;
pub const NR_SWITCH: usize = !0;
pub const NR_RET_FROM_SYSCALL: usize = NR_SWITCH - 1;
pub const NR_DEBUG_SYSCALL: usize = NR_SWITCH - 2;
pub const DISABLE_LOCAL_IRQ_BASEPRI: u8 = irq::IRQ_PRIORITY_FOR_SCHEDULER;

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn bk_handle_hardfault() {
    handle_hardfault()
}

#[no_mangle]
pub unsafe extern "C" fn handle_systick() {
    crate::arch::blueos_kernel_handle_timer_tick();
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
    pub static mut __sys_stack_start: u8;
    pub static mut __sys_stack_end: u8;
}

macro_rules! disable_interrupt {
    () => {
        "
        cpsid i
        "
    };
}

macro_rules! enable_interrupt {
    () => {
        "
        cpsie i
        "
    };
}

pub extern "C" fn reset_msp_and_start_schedule(msp: *mut u8, cont: extern "C" fn() -> !) {
    let sp = prepare_schedule();
    unsafe {
        core::arch::asm!(
            "
            msr psp, {sp}
            msr msp, {msp}
            ",
            // Reset handler is special, see
            // https://stackoverflow.com/questions/59008284/if-the-main-function-is-called-inside-the-reset-handler-how-other-interrupts-ar
            "
            ldr {tmp}, ={thumb}
            msr xpsr, {tmp}
            ldr {tmp}, ={ctrl}
            msr control, {tmp}
            ldr lr, =0
            msr basepri, {basepri}
            cpsie i
            bx {cont}
            ",
            options(nostack, noreturn),
            thumb = const THUMB_MODE,
            ctrl = const CONTROL,
            msp = in(reg) msp,
            sp = in(reg) sp,
            tmp = in(reg) 0,
            cont = in(reg) cont,
            basepri = in(reg) DISABLE_LOCAL_IRQ_BASEPRI,
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
#[cfg(not(target_abi = "eabihf"))]
macro_rules! store_callee_saved_regs {
    () => {
        "
        mrs r12, psp
        stmdb r12!, {{r4-r11}}
        "
    };
}

#[cfg(not(target_abi = "eabihf"))]
macro_rules! load_callee_saved_regs {
    () => {
        "
        ldmia r12!, {{r4-r11}}
        msr psp, r12
        "
    };
}

#[cfg(target_abi = "eabihf")]
macro_rules! store_callee_saved_regs {
    () => {
        "
        mrs r12, psp
        vstmdb r12!, {{s16-s31}}
        stmdb r12!, {{r4-r11}}
        "
    };
}

#[cfg(target_abi = "eabihf")]
macro_rules! load_callee_saved_regs {
    () => {
        "
        ldmia r12!, {{r4-r11}}
        vldmia r12!, {{s16-s31}}
        msr psp, r12
        "
    };
}

#[inline(always)]
pub(crate) extern "C" fn post_pendsv() {
    SCB::set_pendsv();
    unsafe { core::arch::asm!("isb", options(nostack),) }
}

#[naked]
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
    )
}

extern "C" fn syscall_handler(ctx: &mut Context) {
    let sc = crate::arch::SyscallRequest {
        nr: ctx.r7,
        args: [ctx.r0, ctx.r1, ctx.r2, ctx.r3, ctx.r4, ctx.r5],
    };
    // r0 should contain the return value.
    ctx.r0 = crate::arch::blueos_kernel_dispatch_syscall(&sc);
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
    crate::arch::blueos_kernel_save_context_finish_hook(
        hook_ptr.cast(),
        ctx as *const _ as usize,
    )
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
            .byte_offset(offset_of!(Context, pc) as isize)
            .write_volatile(syscall_stub as usize);
        dup_ctx
            .byte_offset(offset_of!(Context, r0) as isize)
            .write_volatile(ctx as *const _ as usize);
        dup_ctx
            .byte_offset(offset_of!(Context, xpsr) as isize)
            .write_volatile(ctx.xpsr & !(1 << 9))
    }
    base
}

#[naked]
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
        next_thread_sp = sym crate::arch::blueos_kernel_relinquish_me_and_return_next_sp,
        basepri = const DISABLE_LOCAL_IRQ_BASEPRI,
    )
}

#[inline]
pub extern "C" fn enable_local_irq() {
    unsafe {
        core::arch::asm!(
            "msr basepri, {}",
            in(reg) 0,
            options(nostack)
        )
    }
}

#[inline]
pub extern "C" fn disable_local_irq() {
    unsafe {
        core::arch::asm!(
            "msr basepri, {}",
            "isb",
            in(reg) DISABLE_LOCAL_IRQ_BASEPRI,
            options(nostack),
        )
    }
}

#[coverage(off)]
#[cfg_attr(debug, inline(never))]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old: usize;
    unsafe {
        core::arch::asm!(
            concat!(
                "
                mrs {old}, basepri
                msr basepri, {val}
                isb
                ",
            ),
            old = out(reg) old,
            val = in(reg) DISABLE_LOCAL_IRQ_BASEPRI,
            options(nostack)
        )
    }
    atomic::compiler_fence(Ordering::SeqCst);
    old
}

#[coverage(off)]
#[cfg_attr(debug, inline(never))]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    atomic::compiler_fence(Ordering::SeqCst);
    unsafe {
        core::arch::asm!(
        "msr basepri, {}", 
        in(reg) old,
        options(nostack))
    }
}

#[inline]
pub extern "C" fn idle() {
    unsafe { core::arch::asm!("wfi") }
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mov {}, sp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn current_msp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mrs {}, msp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn current_psp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mrs {}, psp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline(always)]
pub extern "C" fn pend_switch_context() {
    post_pendsv();
}

#[inline]
pub extern "C" fn current_cpu_id() -> usize {
    0
}

#[inline]
pub extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!(
            "mrs {}, basepri",
            out(reg) x, options(nostack)
        );
    };
    x == 0
}

#[inline]
pub extern "C" fn is_in_interrupt() -> bool {
    cortex_m::peripheral::SCB::vect_active() != cortex_m::peripheral::scb::VectActive::ThreadMode
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
                core::mem::size_of::<IsrContext>(),
                core::mem::size_of::<usize>() * 26
            );
            assert_eq!(
                core::mem::size_of::<Context>(),
                core::mem::size_of::<IsrContext>() + 8 * 4 + 16 * 4
            );
        }
        #[cfg(not(target_abi = "eabihf"))]
        {
            assert_eq!(
                core::mem::size_of::<IsrContext>(),
                core::mem::size_of::<usize>() * 8
            );
            assert_eq!(
                core::mem::size_of::<Context>(),
                core::mem::size_of::<IsrContext>() + 8 * 4
            );
        }
    }
}
