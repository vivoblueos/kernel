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
    claim_switch_context, disable_local_irq, enable_local_irq, Context, IsrContext, NR_SWITCH,
};
use crate::{
    boards::handle_plic_irq,
    debug,
    irq::{enter_irq, leave_irq},
    rv_restore_context, rv_restore_context_epilogue, rv_save_context, rv_save_context_prologue,
    scheduler,
    scheduler::ContextSwitchHookHolder,
    support::sideeffect,
    syscalls::{dispatch_syscall, Context as ScContext},
    thread,
    thread::Thread,
};
use core::{
    mem::offset_of,
    sync::atomic::{compiler_fence, fence, Ordering},
};

pub(crate) const INTERRUPT_MASK: usize = 1usize << (usize::BITS - 1);
pub(crate) const TIMER_INT: usize = INTERRUPT_MASK | 0x7;
pub(crate) const ECALL: usize = 0xB;
pub(crate) const EXTERN_INT: usize = INTERRUPT_MASK | 0xB;

type ContextSwitcher =
    extern "C" fn(to_sp: usize, hook: Option<&mut ContextSwitchHookHolder>) -> usize;

#[naked]
extern "C" fn switch_stack_with_hook(
    to_sp: usize,
    hook: Option<&mut ContextSwitchHookHolder>,
    ra: usize,
    switcher: ContextSwitcher,
) -> ! {
    unsafe { core::arch::naked_asm!("mv sp, a0", "mv ra, a2", "jalr x0, a3, 0") }
}

// trap_handler decides whether nested interrupt is allowed.
#[repr(align(4))]
#[naked]
pub(crate) unsafe extern "C" fn trap_entry() {
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
            addi a3, a3, 14 // Get the address of instruction which is after calling handle_trap.
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
        enter_irq = sym enter_irq,
        leave_irq = sym leave_irq,
        handle_trap = sym handle_trap,
        ra = const offset_of!(Context, ra),
        stack_size = const core::mem::size_of::<Context>(),
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
                mstatus = in(reg) self.isr_ctx.mstatus,
                mcause = in(reg) self.isr_ctx.mcause,
                mtval = in(reg) self.isr_ctx.mtval,
                mepc = in(reg) self.isr_ctx.mepc,
            )
        }
    }
}

extern "C" fn handle_switch(to_sp: usize, hook: Option<&mut ContextSwitchHookHolder>) -> usize {
    scheduler::save_context_finish_hook(hook);
    // Clear MPIE, since we assumes every thread should be resumed
    // with local irq enabled.
    unsafe {
        core::arch::asm!(
            "csrs mstatus, {val}",
            val = in(reg) super::MSTATUS_MPIE,
            options(nostack),
        )
    }
    to_sp
}

fn handle_ecall_switch(from: &Context, ra: usize) -> usize {
    let saved_sp_ptr: *mut usize = unsafe { from.a0 as *mut usize };
    if !saved_sp_ptr.is_null() {
        sideeffect();
        unsafe { saved_sp_ptr.write_volatile(from as *const _ as usize) };
    }
    let to_sp = from.a1;
    let hook_ptr = from.a2 as *mut ContextSwitchHookHolder;
    let hook = if hook_ptr.is_null() {
        sideeffect();
        None
    } else {
        sideeffect();
        Some(unsafe { &mut *hook_ptr })
    };
    switch_stack_with_hook(to_sp, hook, ra, handle_switch)
}

#[inline(never)]
extern "C" fn handle_ecall(ctx: &mut Context, cont: usize) -> usize {
    let sp = ctx as *const _ as usize;
    ctx.mepc += 4;
    if ctx.a7 == NR_SWITCH {
        return handle_ecall_switch(ctx, cont);
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

#[inline(never)]
fn might_switch_context(from: &Context, ra: usize) -> usize {
    let old_sp = from as *const _ as usize;
    if !claim_switch_context() {
        return old_sp;
    }
    let this_thread = scheduler::current_thread_ref();
    let Some(next) = scheduler::next_preferred_thread(this_thread.priority()) else {
        return old_sp;
    };
    this_thread.lock().set_saved_sp(old_sp);
    let to_sp = next.saved_sp();
    let mut hooks = ContextSwitchHookHolder::new(next);
    hooks.set_prev_thread_target_state(thread::READY);
    switch_stack_with_hook(to_sp, Some(&mut hooks), ra, handle_switch)
}

extern "C" fn handle_trap(ctx: &mut Context, mcause: usize, mtval: usize, cont: usize) -> usize {
    let sp = ctx as *const _ as usize;
    match mcause {
        EXTERN_INT => {
            handle_plic_irq(ctx, mcause, mtval);
            sp
        }
        TIMER_INT => {
            crate::time::handle_tick_increment();
            might_switch_context(ctx, cont)
        }
        ECALL => handle_ecall(ctx, cont),
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
