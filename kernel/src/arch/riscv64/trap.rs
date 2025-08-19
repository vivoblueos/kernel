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

use super::{disable_local_irq, enable_local_irq, Context, IsrContext, NR_SWITCH};
use crate::{
    boards::{handle_plic_irq, set_timeout_after},
    debug,
    irq::{enter_irq, leave_irq},
    rv64_restore_context, rv64_restore_context_epilogue, rv64_save_context,
    rv64_save_context_prologue, scheduler,
    scheduler::ContextSwitchHookHolder,
    support::sideeffect,
    syscalls::{dispatch_syscall, Context as ScContext},
    thread::Thread,
};
use core::{
    mem::offset_of,
    sync::atomic::{compiler_fence, fence, Ordering},
};

pub(crate) const INTERRUPT_MASK: usize = 1usize << 63;
pub(crate) const TIMER_INT: usize = INTERRUPT_MASK | 0x7;
pub(crate) const ECALL: usize = 0xB;
pub(crate) const EXTERN_INT: usize = INTERRUPT_MASK | 0xB;

// trap_handler decides whether nested interrupt is allowed.
#[repr(align(4))]
#[naked]
pub(crate) unsafe extern "C" fn trap_entry() {
    core::arch::naked_asm!(
        concat!(
            rv64_save_context_prologue!(),
            rv64_save_context!(),
            "
            mv s1, sp
            csrr s2, mcause
            csrr s3, mtval
            call {enter_irq}
            mv a0, s1
            mv a1, s2
            mv a2, s3
            call {handle_trap}
            mv sp, a0
            call {leave_irq}
            mv a0, s1
            mv a1, sp
            mv a2, s2
            call {might_switch}
            mv sp, a0
            ",
            rv64_restore_context!(),
            rv64_restore_context_epilogue!(),
            "
            fence rw, rw
            mret
            "
        ),
        enter_irq = sym enter_irq,
        leave_irq = sym leave_irq,
        handle_trap = sym handle_trap,
        ra = const offset_of!(Context, ra),
        stack_size = const core::mem::size_of::<Context>(),
        might_switch = sym might_switch,
        gp = const offset_of!(Context, gp),
        tp = const offset_of!(Context, tp),
        t0 = const offset_of!(Context, t0),
        t1 = const offset_of!(Context, t1),
        t2 = const offset_of!(Context, t2),
        t3 = const offset_of!(Context, t3),
        t4 = const offset_of!(Context, t4),
        t5 = const offset_of!(Context, t5),
        t6 = const offset_of!(Context, t6),
        a0 = const offset_of!(Context, a0),
        a1 = const offset_of!(Context, a1),
        a2 = const offset_of!(Context, a2),
        a3 = const offset_of!(Context, a3),
        a4 = const offset_of!(Context, a4),
        a5 = const offset_of!(Context, a5),
        a6 = const offset_of!(Context, a6),
        a7 = const offset_of!(Context, a7),
        fp = const offset_of!(Context, fp),
        s1 = const offset_of!(Context, s1),
        s2 = const offset_of!(Context, s2),
        s3 = const offset_of!(Context, s3),
        s4 = const offset_of!(Context, s4),
        s5 = const offset_of!(Context, s5),
        s6 = const offset_of!(Context, s6),
        s7 = const offset_of!(Context, s7),
        s8 = const offset_of!(Context, s8),
        s9 = const offset_of!(Context, s9),
        s10 = const offset_of!(Context, s10),
        s11 = const offset_of!(Context, s11),
        mepc = const offset_of!(Context, mepc),
    )
}

#[derive(Default, Debug)]
struct SyscallGuard {
    isr_ctx: IsrContext,
}

impl SyscallGuard {
    pub fn new() -> Self {
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
        leave_irq();
        enable_local_irq();
        g
    }
}

impl Drop for SyscallGuard {
    fn drop(&mut self) {
        disable_local_irq();
        enter_irq();
        compiler_fence(Ordering::SeqCst);
        unsafe {
            core::arch::asm!(
                "csrw mstatus, {mstatus}",
                "csrw mcause, {mcause}",
                "csrw mtval, {mtval}",
                "csrw mepc, {mepc}",
                "fence rw, rw",
                mstatus = in(reg) self.isr_ctx.mstatus,
                mcause = in(reg) self.isr_ctx.mcause,
                mtval = in(reg) self.isr_ctx.mtval,
                mepc = in(reg) self.isr_ctx.mepc,
            )
        }
    }
}

#[inline(never)]
extern "C" fn handle_ecall(ctx: &mut Context) -> usize {
    let sp = ctx as *const _ as usize;
    ctx.mepc += 4;
    if ctx.a7 == NR_SWITCH {
        return ctx.a1;
    }
    {
        compiler_fence(Ordering::SeqCst);
        let scg = SyscallGuard::new();
        let sc = ScContext {
            nr: ctx.a7,
            args: [ctx.a0, ctx.a1, ctx.a2, ctx.a3, ctx.a4, ctx.a5],
        };
        ctx.a0 = dispatch_syscall(&sc);
        compiler_fence(Ordering::SeqCst);
    }
    sp
}

extern "C" fn might_switch(from: &Context, to: &Context, mcause: usize) -> usize {
    let from_ptr = from as *const _;
    let to_ptr = to as *const _;
    if from_ptr == to_ptr {
        return from_ptr as usize;
    }
    // Currently we only handle this case.
    assert!(mcause == ECALL && from.a7 == NR_SWITCH);
    assert_eq!(to_ptr as usize, from.a1);
    let sp = from_ptr as usize;
    let saved_sp_ptr: *mut usize = unsafe { from.a0 as *mut usize };
    if !saved_sp_ptr.is_null() {
        sideeffect();
        // FIXME: rustc opt the write out if not setting it volatile.
        unsafe { saved_sp_ptr.write_volatile(sp) };
    }
    let hook: *mut ContextSwitchHookHolder = unsafe { from.a2 as *mut ContextSwitchHookHolder };
    if !hook.is_null() {
        sideeffect();
        unsafe {
            scheduler::save_context_finish_hook(Some(&mut *hook));
        }
    }
    // Clear MPIE, since we assumes every thread should be resumed
    // with local irq enabled.
    unsafe {
        core::arch::asm!(
            "csrs mstatus, {val}",
            val = in(reg) super::MSTATUS_MPIE,
        )
    }
    from.a1
}

extern "C" fn handle_trap(ctx: &mut Context, mcause: usize, mtval: usize) -> usize {
    let sp = ctx as *const _ as usize;
    match mcause {
        EXTERN_INT => {
            handle_plic_irq(ctx, mcause, mtval);
            sp
        }
        TIMER_INT => {
            crate::time::handle_tick_increment();
            sp
        }
        ECALL => handle_ecall(ctx),
        _ => {
            let t = scheduler::current_thread();
            panic!(
                "[C#{}:0x{:x}] Unexpected trap: context: {:?}, mcause: 0x{:x}, mtval: 0x{:x}",
                super::current_cpu_id(),
                Thread::id(&t),
                ctx,
                mcause,
                mtval
            );
        }
    }
}
