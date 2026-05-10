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
    context::ExceptionContext,
    irq::{self, Vector},
};
use crate::SyscallRequest;
use core::mem::offset_of;

pub const NR_SWITCH: usize = !0;
pub const NR_RET_FROM_SYSCALL: usize = NR_SWITCH - 1;
pub const NR_DEBUG_SYSCALL: usize = NR_SWITCH - 2;
pub const DISABLE_LOCAL_IRQ_BASEPRI: u8 = irq::IRQ_PRIORITY_FOR_SCHEDULER;

unsafe extern "C" {
    fn bk_handle_hardfault();
    fn handle_memfault();
    fn handle_hardfault();
}

#[no_mangle]
#[link_section = ".exception.handlers"]
#[used]
pub static __EXCEPTION_HANDLERS__: [Vector; 15] = build_exception_handlers();

const fn build_exception_handlers() -> [Vector; 15] {
    let mut tbl = [Vector { reserved: 0 }; 15];
    tbl[0] = Vector {
        handler: super::cortex_m_boot_entry,
    };
    tbl[1] = Vector {
        handler: handle_hardfault,
    };
    tbl[2] = Vector {
        handler: bk_handle_hardfault,
    };
    tbl[3] = Vector {
        handler: handle_memfault,
    };
    tbl[4] = Vector {
        handler: handle_hardfault,
    };
    tbl[5] = Vector {
        handler: handle_hardfault,
    };
    tbl[10] = Vector { handler: handle_svc };
    tbl[13] = Vector {
        handler: handle_pendsv,
    };
    tbl[14] = Vector {
        handler: handle_systick,
    };
    tbl
}

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

pub unsafe extern "C" fn handle_systick() {
    unsafe { crate::blueos_kernel_handle_timer_tick() };
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

extern "C" fn syscall_handler(ctx: &mut ExceptionContext) {
    let sc = SyscallRequest {
        nr: ctx.r7,
        args: [ctx.r0, ctx.r1, ctx.r2, ctx.r3, ctx.r4, ctx.r5],
    };
    ctx.r0 = unsafe { crate::blueos_kernel_dispatch_syscall(&sc) };
}

#[naked]
unsafe extern "C" fn syscall_stub(_ctx: *mut ExceptionContext) -> ! {
    core::arch::naked_asm!(
        "
        push {{r0, lr}}
        bl {syscall_handler}
        pop {{r0, lr}}
        ldr r7, ={syscall_ret}
        svc 0
        ",
        syscall_handler = sym syscall_handler,
        syscall_ret = const NR_RET_FROM_SYSCALL,
    )
}

#[inline(never)]
fn handle_svc_switch(ctx: &ExceptionContext) -> usize {
    debug_assert_eq!(ctx.r7, NR_SWITCH);
    let hook = ctx.r0 as *mut core::ffi::c_void;
    debug_assert!(!hook.is_null());
    unsafe { crate::blueos_kernel_save_context_finish_hook(hook, ctx as *const _ as usize) }
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn bk_debug_syscall(ctx: &ExceptionContext) -> usize {
    ctx as *const _ as usize
}

extern "C" fn handle_syscall(ctx: &ExceptionContext) -> usize {
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

    // Due to Cortex-M's limitation, we split syscall handling into 2 phases:
    // P0:
    //   Switch stack, go back to thread mode and run handler. Then syscall
    //   NR_RET_FROM_SYSCALL to go back to ISR mode.
    // P1:
    //   Switch stack and return to the normal control flow of thread mode.

    // Duplicate ctx so that we can exit to thread mode to handle syscalls.
    // This mirrors the old kernel-side implementation that used
    // RegionalObjectBuilder::write_after_start() followed by sideeffect().
    let size = core::mem::size_of::<ExceptionContext>();
    let base = unsafe { (ctx as *const ExceptionContext).byte_offset(-(size as isize)) as usize };
    debug_assert_eq!(base % core::mem::align_of::<ExceptionContext>(), 0);
    let dup_ctx = base as *mut ExceptionContext as *mut usize;
    unsafe {
        // bluekernel_arch cannot depend on kernel support helpers. Use a
        // volatile write instead of a plain write plus sideeffect(): this frame
        // is consumed by the Cortex-M exception-return sequence after PSP is
        // updated, so normal Rust code never reads it and release builds may
        // otherwise optimize the full frame copy away.
        core::ptr::write_volatile(base as *mut ExceptionContext, *ctx);
        dup_ctx
            .byte_offset(offset_of!(ExceptionContext, pc) as isize)
            .write_volatile(syscall_stub as usize);
        dup_ctx
            .byte_offset(offset_of!(ExceptionContext, r0) as isize)
            .write_volatile(ctx as *const _ as usize);
        dup_ctx
            .byte_offset(offset_of!(ExceptionContext, xpsr) as isize)
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
        next_thread_sp = sym crate::blueos_kernel_relinquish_me_and_return_next_sp,
        basepri = const DISABLE_LOCAL_IRQ_BASEPRI,
    )
}
