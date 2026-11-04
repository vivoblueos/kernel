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
    arch,
    boards::clear_ipi,
    debug,
    irq::{enter_irq, leave_irq},
    rv_restore_context, rv_restore_context_epilogue, rv_save_context, rv_save_context_prologue,
    scheduler,
    scheduler::ContextSwitchHookHolder,
    support::sideeffect,
    syscalls::{dispatch_syscall, Context as ScContext},
    thread,
    thread::Thread,
    types::Arc,
};
use core::{
    mem::offset_of,
    sync::atomic::{compiler_fence, fence, Ordering},
};

pub(crate) const INTERRUPT_MASK: usize = 1usize << (usize::BITS - 1);
pub(crate) const TIMER_INT: usize = INTERRUPT_MASK | 0x7;
pub(crate) const EXTERN_INT: usize = INTERRUPT_MASK | 0xB;
pub(crate) const ECALL: usize = 0xB;
/// `ecall` from **U-mode** (cause 8) — a user process asking for a syscall.
///
/// Deliberately distinct from [`ECALL`]: causes 8/9/11 are the U/S/M flavours
/// of the same instruction. Matching only 11 means a syscall raised by a user
/// process falls through to the catch-all arm and wedges the machine, which is
/// exactly what a working user/kernel boundary cannot do.
pub(crate) const ECALL_FROM_U: usize = 8;
/// `ecall` from S-mode (cause 9). Unused — the kernel runs in M-mode — but
/// named so the three numbers are never confused for one another.
#[allow(dead_code)]
pub(crate) const ECALL_FROM_S: usize = 9;
/// Instruction page fault (cause 12).
pub(crate) const INST_PAGE_FAULT: usize = 12;
/// Instruction access fault (cause 1): the fetch was denied before translation
/// even mattered — PMP, or a bare-mode address with no memory behind it.
pub(crate) const INST_ACCESS_FAULT: usize = 1;
/// Load page fault (cause 13).
pub(crate) const LOAD_PAGE_FAULT: usize = 13;
/// Store/AMO page fault (cause 15).
pub(crate) const STORE_PAGE_FAULT: usize = 15;
/// Illegal instruction (cause 2).
#[allow(dead_code)]
pub(crate) const ILLEGAL_INSTRUCTION: usize = 2;
pub(crate) const MSI: usize = INTERRUPT_MASK | 0x3;

type ContextSwitcher = extern "C" fn(hook: &mut ContextSwitchHookHolder, old_sp: usize) -> usize;

#[cfg_attr(compatible_old_toolchain, naked)]
#[cfg_attr(not(compatible_old_toolchain), unsafe(naked))]
extern "C" fn switch_stack_with_hook(
    hook: &mut ContextSwitchHookHolder,
    old_sp: usize,
    to_sp: usize,
    ra: usize,
    switcher: ContextSwitcher,
) -> ! {
    unsafe { core::arch::naked_asm!("mv sp, a2", "mv ra, a3", "jalr x0, a4, 0") }
}

// trap_handler decides whether nested interrupt is allowed.
#[cfg_attr(not(compatible_old_toolchain), rustc_align(4))]
#[cfg_attr(compatible_old_toolchain, repr(align(4)))]
#[cfg_attr(compatible_old_toolchain, link_section = ".trap.handler")]
#[cfg_attr(not(compatible_old_toolchain), unsafe(link_section = ".trap.handler"))]
#[cfg_attr(compatible_old_toolchain, naked)]
#[cfg_attr(not(compatible_old_toolchain), unsafe(naked))]
pub(crate) unsafe extern "C" fn trap_entry() {
    core::arch::naked_asm!(
        concat!(
            // --- Trap entry: get onto a kernel stack before touching memory ---
            //
            // `rv_save_context_prologue!` writes the context at the *current*
            // `sp`, which is fine for an M-mode trap (that is a thread stack)
            // but fatal for a U-mode one: the context would land on the user
            // stack, which may be unmapped, read-only, or simply bogus, and
            // the very first store would double-fault.
            //
            // RISC-V has no hardware stack switch, so `mscratch` is the
            // scratchpad for it. The kernel keeps it pointing at the top of the
            // current thread's kernel stack while user code runs, and zero
            // while the kernel itself runs. `csrrw sp, mscratch, sp` is the one
            // instruction that can do the swap with no temporary register —
            // which is the whole point, since no register has been saved yet.
            //
            // Deciding *whether* to keep the swap has to happen without
            // clobbering anything either, so the test is on the value just
            // loaded into `sp`: nonzero means `mscratch` held a kernel stack
            // (U-mode trap, `sp` is now correct); zero means it held the M-mode
            // convention (swap back, restoring both `sp` and `mscratch`).
            // Branching on `sp` costs nothing here because between the two
            // swaps `sp` is never dereferenced.
            "
            csrrw sp, mscratch, sp
            beqz sp, 90f
            j 91f
            90:
            csrrw sp, mscratch, sp
            91:
            ",
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
            // --- Trap return: undo the entry swap, if there was one ---
            //
            // The epilogue has already popped the context, so `sp` is now the
            // top of the kernel stack (U-mode return) or the thread's `sp`
            // (M-mode return), and `rv_restore_context!` has refilled
            // `mscratch` from the context: the user `sp`, or zero.
            //
            // The same swap therefore does the right thing in both cases, and
            // leaves `mscratch` holding exactly what the next trap needs — the
            // kernel stack top for a U-mode return, zero for an M-mode one.
            // Note this runs *after* the context was popped but *before* `mret`:
            // `mret` only changes privilege and jumps, so `sp` has to be the
            // user stack by then, and there is no register left to do it with.
            "
            csrrw sp, mscratch, sp
            beqz sp, 92f
            j 93f
            92:
            csrrw sp, mscratch, sp
            93:
            mret
            "
        ),
        enter_irq = sym enter_irq,
        leave_irq = sym leave_irq,
        handle_trap = sym handle_trap,
        ra = const offset_of!(Context, ra),
        stack_size = const core::mem::size_of::<Context>(),
        mscratch = const offset_of!(Context, mscratch),
        mpp_mask = const super::PP_MASK,
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
#[must_use]
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

extern "C" fn handle_switch(hook: &mut ContextSwitchHookHolder, old_sp: usize) -> usize {
    scheduler::save_context_finish_hook(hook, old_sp)
}

fn handle_ecall_switch(from: &Context, ra: usize) -> usize {
    let hook_ptr = from.a0 as *mut ContextSwitchHookHolder;
    debug_assert!(!hook_ptr.is_null());
    let hook = unsafe { &mut *hook_ptr };
    let next_saved_sp = scheduler::spin_until_ready_to_run(unsafe { hook.next_thread() });
    let old_sp = from as *const _ as usize;
    switch_stack_with_hook(hook, old_sp, next_saved_sp, ra, handle_switch)
}

#[inline(never)]
extern "C" fn handle_ecall(ctx: &mut Context, cont: usize) -> usize {
    let sp = ctx as *const _ as usize;
    ctx.mepc += 4;
    if ctx.a7 == NR_SWITCH {
        // `NR_SWITCH` is the scheduler's private ecall, not a syscall: `a0` is
        // read as a *kernel* pointer to a `ContextSwitchHookHolder` and
        // dereferenced. It is only ever raised by `switch_context_with_hook`
        // from M-mode. Before the user/kernel boundary existed that was safe by
        // construction — nothing but the kernel could reach here. A user
        // process can set `a7` to anything, so honouring it would turn `a0`
        // into an arbitrary kernel pointer: a read/write primitive on kernel
        // memory picked entirely by user code. Refuse it.
        if super::previous_privilege() == super::PP_U {
            crate::kearly_println!(
                "[C#{}:0x{:x}] user process attempted the kernel-private NR_SWITCH ecall — EPERM",
                super::current_cpu_id(),
                Thread::id(scheduler::current_thread_ref())
            );
            ctx.a0 = -(libc::EPERM as isize) as usize;
            return sp;
        }
        return handle_ecall_switch(ctx, cont);
    }
    {
        compiler_fence(Ordering::SeqCst);
        let scg = SyscallGuard::new();
        let sc = ScContext {
            nr: ctx.a7,
            args: [ctx.a0, ctx.a1, ctx.a2, ctx.a3, ctx.a4, ctx.a5],
            // `fork` needs the whole register file, not just `a0`-`a5`.
            frame: ctx as *mut Context as usize,
        };
        let ret = dispatch_syscall(&sc);
        // A signal delivered while this syscall ran has already rewritten the
        // frame to enter its handler with `a0 = signum`. Keep that value in
        // `a0`; writing the syscall result would replace the handler argument.
        #[cfg(target_arch = "riscv64")]
        let ret = if crate::scheduler::is_schedule_ready()
            && scheduler::current_thread_ref().take_signal_redirect()
        {
            ctx.a0
        } else {
            ret
        };
        ctx.a0 = ret;
        // `execve` does not return to the caller: it repoints the saved frame
        // instead, so the `mret` that ends this syscall lands at the new
        // program's entry with the new stack. Redirecting the return here is
        // what makes exec work without a separate "return to user" path.
        #[cfg(target_arch = "riscv64")]
        if let Some(outcome) = crate::user::take_exec_outcome() {
            ctx.mepc = outcome.entry;
            ctx.mscratch = outcome.sp;
        }
        compiler_fence(Ordering::SeqCst);
    }
    sp
}

// FIXME: We have added too much complexity switching the stack, we should use
// another way to switch context on RV.
fn might_switch_context(from: &Context, ra: usize) -> usize {
    let old_sp = from as *const _ as usize;
    if !claim_switch_context() {
        return old_sp;
    }
    let old = scheduler::current_thread_ref();
    if old.preempt_count() != 0 {
        return old_sp;
    }
    let Some(next) = scheduler::next_preferred_thread(old.priority()) else {
        return old_sp;
    };
    debug_assert_eq!(next.state(), thread::READY);
    debug_assert_ne!(Thread::id(old), Thread::id(&next));
    let mut hook = ContextSwitchHookHolder::new(next);
    if Thread::id(old) == Thread::id(scheduler::current_idle_thread_ref()) {
        let res = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert_eq!(res, Ok(()));
    } else {
        let res = scheduler::queue_ready_thread(thread::RUNNING, unsafe { Arc::clone_from(old) });
        debug_assert_eq!(res, Ok(()));
    };
    let next_saved_sp = scheduler::spin_until_ready_to_run(unsafe { hook.next_thread() });
    switch_stack_with_hook(&mut hook, old_sp, next_saved_sp, ra, handle_switch)
}

extern "C" fn handle_trap(ctx: &mut Context, mcause: usize, mtval: usize, cont: usize) -> usize {
    debug_assert!(!super::local_irq_enabled());
    // Remember this thread's U-mode frame for signal delivery. A kernel-mode
    // trap must leave the previous value alone: the frame underneath is still
    // the one the thread will return to.
    if super::previous_privilege() == super::PP_U {
        scheduler::current_thread_ref().set_trap_frame(ctx as *mut Context as usize);
    }
    let sp = ctx as *const _ as usize;
    match mcause & (INTERRUPT_MASK | 0x3f) {
        #[cfg(has_plic)]
        EXTERN_INT => {
            use crate::boards::handle_plic_irq;
            handle_plic_irq(ctx, mcause, mtval);
            might_switch_context(ctx, cont)
        }
        #[cfg(has_mtime)]
        TIMER_INT => {
            crate::time::handle_clock_interrupt();
            might_switch_context(ctx, cont)
        }
        // Cause 11 (M-mode) and cause 8 (U-mode) are both `ecall`; a user
        // process raising a syscall arrives as the latter.
        ECALL | ECALL_FROM_U => handle_ecall(ctx, cont),
        // A user process touching a page that is inside one of its regions but
        // has no frame yet (demand paging), or a page that is read-only because
        // it is copy-on-write and this access is a store. Anything else is a
        // real fault: the process's SIGSEGV disposition decides whether it is
        // handed to a handler or ends the process — which is what keeps a wild
        // pointer inside the process that made it.
        INST_PAGE_FAULT | LOAD_PAGE_FAULT | STORE_PAGE_FAULT => {
            #[cfg(target_arch = "riscv64")]
            {
                if super::previous_privilege() == super::PP_U {
                    let need = if mcause & 0x3f == STORE_PAGE_FAULT {
                        crate::arch::riscv::mmu::Perms::WRITE
                    } else if mcause & 0x3f == INST_PAGE_FAULT {
                        crate::arch::riscv::mmu::Perms::EXEC
                    } else {
                        crate::arch::riscv::mmu::Perms::READ
                    };
                    if crate::user::handle_page_fault(mtval, need) {
                        // `mepc` was not advanced, so the `mret` re-executes
                        // the faulting instruction — this time successfully.
                        return sp;
                    }
                    // Genuine fault: a bad access that is not demand paging or
                    // copy-on-write. If the program installed a handler for
                    // SIGSEGV, the trap return is redirected into it with the
                    // interrupted state saved on its own stack; the handler's
                    // `ret` reaches the trampoline, whose `sigreturn` puts the
                    // thread back where it faulted. Without a handler the
                    // process ends here.
                    if crate::signal::delivery::deliver_fault(
                        ctx,
                        crate::signal::posix::sig::SIGSEGV,
                    ) {
                        return sp;
                    }
                    crate::kearly_println!(
                        "[C#{}:0x{:x}] user fault at 0x{:x} (mcause 0x{:x}) — killing process",
                        super::current_cpu_id(),
                        Thread::id(scheduler::current_thread_ref()),
                        mtval,
                        mcause & 0x3f
                    );
                    scheduler::retire_me();
                }
            }
            unexpected_trap(ctx, mcause, mtval)
        }
        // An instruction access fault from U-mode means the fetch was denied
        // before translation could even report a missing page: either PMP
        // refused it or `satp` was bare while the thread was in U-mode. Neither
        // is recoverable for the process, and falling through to
        // `unexpected_trap` would spin this hart forever, so retire the caller
        // the same way an illegal instruction does.
        INST_ACCESS_FAULT => {
            #[cfg(target_arch = "riscv64")]
            {
                if super::previous_privilege() == super::PP_U {
                    if crate::signal::delivery::deliver_fault(
                        ctx,
                        crate::signal::posix::sig::SIGSEGV,
                    ) {
                        return sp;
                    }
                    crate::kearly_println!(
                        "[C#{}:0x{:x}] user instruction access fault at 0x{:x} (satp=0x{:x}) — killing process",
                        super::current_cpu_id(),
                        Thread::id(scheduler::current_thread_ref()),
                        ctx.mepc,
                        crate::user::current_satp()
                    );
                    scheduler::retire_me();
                }
            }
            unexpected_trap(ctx, mcause, mtval)
        }
        // Cause 2: illegal instruction. A user process executing an undefined
        // instruction is delivered to its SIGILL handler through the same
        // saved-frame path as SIGSEGV; without a handler it ends the process
        // rather than spinning the machine forever in `unexpected_trap`.
        ILLEGAL_INSTRUCTION => {
            #[cfg(target_arch = "riscv64")]
            {
                if super::previous_privilege() == super::PP_U {
                    if crate::signal::delivery::deliver_fault(
                        ctx,
                        crate::signal::posix::sig::SIGILL,
                    ) {
                        return sp;
                    }
                    crate::kearly_println!(
                        "[C#{}:0x{:x}] user illegal instruction at 0x{:x} — killing process",
                        super::current_cpu_id(),
                        Thread::id(scheduler::current_thread_ref()),
                        ctx.mepc
                    );
                    scheduler::retire_me();
                }
            }
            unexpected_trap(ctx, mcause, mtval)
        }
        // For waking up from wfi.
        MSI => {
            clear_ipi(arch::current_cpu_id());
            sp
        }
        #[cfg(not(has_plic))]
        _ if mcause & 0x8000_0000 != 0 => {
            use crate::boards::handle_intc_irq;
            // esp32c3 has another external interrupt number
            handle_intc_irq(ctx, mcause, mtval);
            might_switch_context(ctx, cont)
        }
        _ => unexpected_trap(ctx, mcause, mtval),
    }
}

/// Report a trap the kernel has no recovery for, and stop.
///
/// Deliberately a separate function: the caller's match arm stays a single
/// expression, and the never-returning body keeps its stack frame out of the
/// hot path.
#[cold]
#[inline(never)]
fn unexpected_trap(ctx: &Context, mcause: usize, mtval: usize) -> usize {
    let t = scheduler::current_thread_ref();
    crate::kearly_println!(
        "[C#{}:0x{:x}] Unexpected trap: from_u={} context: {:?}, mcause: 0x{:x}, mtval: 0x{:x}",
        super::current_cpu_id(),
        Thread::id(t),
        super::previous_privilege() == super::PP_U,
        ctx,
        mcause,
        mtval
    );
    loop {
        core::hint::spin_loop();
    }
}
