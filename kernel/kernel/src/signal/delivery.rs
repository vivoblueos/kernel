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

//! Delivery of POSIX signals to user-space handlers.
//!
//! # How a user handler is called
//!
//! On a system with a memory-management unit, a signal handler runs on a
//! separate *signal frame*: the kernel builds a frame on the signal stack,
//! points it at the handler, and the handler returns through a trampoline
//! that restores the interrupted context.
//!
//! BlueKernel has no MMU separation between the kernel and the programs it
//! runs - the user program and the kernel share one address space, and a
//! thread's stack is the same stack the handler would run on. So the frame
//! buys nothing here: the handler can simply be called, and when it returns
//! the thread carries on where it left off.
//!
//! What that means in practice:
//!
//! * The handler runs on the thread's ordinary stack, not on an alternate
//!   signal stack. `sigaltstack()` therefore records the request but does
//!   not switch stacks.
//! * The handler receives only the signal number. The `SA_SIGINFO` variants
//!   (`siginfo_t`, `ucontext_t`) are not provided.
//! * While the handler runs, its own signal is added to the mask, and the
//!   mask is restored afterwards - which is what POSIX requires.
//!
//! Everything else - the disposition table, the per-thread mask, the pending
//! set, `sigprocmask()`, `sigpending()`, `sigsuspend()`, `sigwait()` -
//! behaves as POSIX specifies.

use crate::{process::current_process, scheduler, thread::Thread};
use super::posix::{bit, sig, SignalAction, NSIG, SIG_DFL, SIG_IGN};

/// The register state pushed onto the user stack before a synchronous fault
/// is handed to a user handler.
///
/// The handler runs in U-mode, not in the kernel, because the interrupted
/// state has to be saved before the trap returns. That means the handler's
/// `ret` cannot come back to this trap frame: it lands on the signal
/// trampoline, which issues `sigreturn`, and the kernel restores this frame.
///
/// The thread's signal mask is carried alongside the registers because POSIX
/// restores it when the handler returns, and by then this function is long
/// gone.
#[cfg(target_arch = "riscv64")]
#[repr(C, align(16))]
struct SignalFrame {
    ctx: crate::arch::riscv::Context,
    mask: usize,
}

/// Hands a synchronous fault (page fault, illegal instruction, access fault)
/// to the user handler for `signum`, if one is installed.
///
/// The interrupted register state is written below the faulting stack pointer
/// and the trap return is redirected to `action.handler`. Returns `false` when
/// there is no user handler - the caller then keeps the old behaviour of
/// ending the process - or when the frame cannot be written (a program that
/// faulted with no stack left cannot be given a handler either).
#[cfg(target_arch = "riscv64")]
pub fn deliver_fault(ctx: &mut crate::arch::riscv::Context, signum: usize) -> bool {
    let this = scheduler::current_thread_ref();
    let Some(process) = current_process() else {
        return false;
    };
    let action = process.signals().action(signum);
    if action.handler == SIG_DFL || action.handler == SIG_IGN {
        return false;
    }
    if !push_signal_frame(ctx, signum, &action, this) {
        return false;
    }
    this.note_signal_delivered();
    true
}

/// Marks that the pending signal `signum` arrived while the thread was inside
/// a syscall, and redirects the ecall's return frame into the handler.
///
/// Async signals have no fault of their own: the thread is somewhere in the
/// kernel, and accounting for it as a synchronous fault would resume at the
/// wrong `mepc`. This pushes a frame anyway and lets the syscall's own return
/// path land in the handler. The caller must be a syscall-context thread whose
/// `trap_frame` is the U-mode frame that will be `mret`ed.
#[cfg(target_arch = "riscv64")]
pub fn deliver_async(
    ctx: &mut crate::arch::riscv::Context,
    signum: usize,
    action: &SignalAction,
    thread: &'static Thread,
) -> bool {
    if !push_signal_frame(ctx, signum, action, thread) {
        return false;
    }
    // The ecall path writes `a0` with the dispatch result after this returns.
    // `a0` belongs to the handler now, so the write has to be suppressed.
    thread.set_signal_redirect();
    true
}

/// Builds the signal frame on the user stack and rewrites `ctx` so the next
/// `mret` enters the handler with the trampoline as its return address.
#[cfg(target_arch = "riscv64")]
fn push_signal_frame(
    ctx: &mut crate::arch::riscv::Context,
    signum: usize,
    action: &SignalAction,
    thread: &'static Thread,
) -> bool {
    let size = core::mem::size_of::<SignalFrame>();
    let Some(frame_va) = ctx.mscratch.checked_sub(size).map(|a| a & !0xf) else {
        return false;
    };
    let frame = SignalFrame {
        ctx: ctx.clone(),
        mask: thread.signal_mask().blocked(),
    };
    let bytes = unsafe {
        core::slice::from_raw_parts(&frame as *const SignalFrame as *const u8, size)
    };
    if crate::user::copy_to_user(frame_va, bytes).is_err() {
        return false;
    }

    // POSIX: the handled signal is blocked while the handler runs up to
    // `sigreturn`, unless `SA_NODEFER`, and `sa_mask` is added on top.
    let mut effective = frame.mask;
    if action.flags & super::posix::SA_NODEFER == 0 {
        effective |= bit(signum);
    }
    effective |= action.mask;
    thread.signal_mask().set_blocked(effective);

    ctx.mscratch = frame_va;
    ctx.mepc = action.handler;
    ctx.ra = crate::user::SIGTRAMPOLINE_VA;
    ctx.a0 = signum;
    true
}

/// Restores the frame built by [`deliver_fault`] after the handler returns.
///
/// Called from the `sigreturn` ecall the trampoline issues. The frame address
/// is the user stack pointer at the ecall, which the handler's own epilogue
/// put back to where the frame starts. Returning `saved.a0` matters: the
/// syscall return path writes it into the frame's `a0`, and for `sigreturn`
/// that is the *interrupted* `a0` rather than a result.
#[cfg(target_arch = "riscv64")]
pub fn sigreturn(frame: *mut crate::arch::riscv::Context) -> isize {
    if frame.is_null() {
        return -(libc::EFAULT as isize);
    }
    let frame_va = unsafe { (*frame).mscratch };
    let mut saved = core::mem::MaybeUninit::<SignalFrame>::uninit();
    let dst = unsafe {
        core::slice::from_raw_parts_mut(
            saved.as_mut_ptr() as *mut u8,
            core::mem::size_of::<SignalFrame>(),
        )
    };
    if crate::user::copy_from_user(dst, frame_va).is_err() {
        return -(libc::EFAULT as isize);
    }
    // SAFETY: `copy_from_user` filled the whole frame, and `SignalFrame` is a
    // plain `repr(C)` struct of integers.
    let saved = unsafe { saved.assume_init() };
    let a0 = saved.ctx.a0 as isize;
    let mask = saved.mask;
    unsafe { *frame = saved.ctx };
    scheduler::current_thread_ref()
        .signal_mask()
        .set_blocked(mask);
    a0
}

/// Delivers the pending POSIX signals of the current thread.
///
/// Returns the number of signals that were handled.
pub fn deliver_pending() -> usize {
    let this = scheduler::current_thread_ref();
    let Some(process) = current_process() else {
        // A thread without a process has no dispositions; the kernel's own
        // signal handling takes care of it.
        return 0;
    };

    let mut handled = 0;
    loop {
        let Some(signum) = super::posix::take_pending(this, Some(&process)) else {
            break;
        };
        let action = process.signals().action(signum);
        if action.handler == SIG_IGN {
            // `take_pending` already discarded it. A signal that is ignored
            // is not "caught", so it does not count as a delivery and does
            // not interrupt `poll()`.
            continue;
        }
        // Count the delivery before applying it: `poll()` compares two
        // readings of this counter to learn that a signal was caught while
        // it was asleep, and by the time the waiter runs again the handler
        // has already come and gone.
        this.note_signal_delivered();
        if action.handler == SIG_DFL {
            handle_default(signum);
            handled += 1;
            continue;
        }
        // A U-mode thread has a trap frame saved on its kernel stack even
        // when it is here from inside a syscall. Redirecting that frame runs
        // the handler in U-mode; calling it directly would run user code with
        // kernel privileges on a kernel stack.
        #[cfg(target_arch = "riscv64")]
        {
            let frame = this.trap_frame();
            if frame != 0 {
                // SAFETY: the trap layer stored this thread's own frame while
                // it was in the kernel, and the kernel stack that holds it
                // stays alive until the frame is returned to.
                let ctx = unsafe { &mut *(frame as *mut crate::arch::riscv::Context) };
                if deliver_async(ctx, signum, &action, this) {
                    handled += 1;
                    continue;
                }
            }
        }
        run_handler(this, &action, signum);
        handled += 1;
    }
    handled
}

/// What a signal does when its disposition is `SIG_DFL`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DefaultAction {
    /// The thread that took the signal is retired.
    Terminate,
    /// The signal is discarded.
    Ignore,
}

/// The default disposition of a signal, as POSIX defines it.
///
/// Three groups are ignored by default - the notification signals
/// (`SIGCHLD`, `SIGURG`, `SIGWINCH`), the job-control signals and `SIGCONT`.
/// Job control itself is not implemented: a thread has no stopped state, so
/// a stop request is discarded rather than deferred, and `SIGCONT` has
/// nothing to continue. Everything else terminates the thread that took it.
///
/// `SIGKILL` is in the terminating group and, as POSIX requires, cannot be
/// caught - `sigaction()` refuses it, so it always reaches this function.
fn default_action(signum: usize) -> DefaultAction {
    match signum {
        // Nothing to report to the program, and nothing to undo.
        sig::SIGCHLD | sig::SIGURG | sig::SIGWINCH => DefaultAction::Ignore,
        // No job control: see the doc comment.
        sig::SIGSTOP | sig::SIGTSTP | sig::SIGTTIN | sig::SIGTTOU | sig::SIGCONT => {
            DefaultAction::Ignore
        }
        // Everything else - the fatal signals, the alarms, `SIGUSR1/2`, and
        // any number this table does not know - terminates the thread.
        _ => DefaultAction::Terminate,
    }
}

/// Applies the default disposition of a signal.
///
/// POSIX says the default action of a terminating signal ends the *process*.
/// This kernel has no way to tear a process down from the thread that took
/// the signal (a process only becomes `Zombie` when its last thread is gone),
/// so the thread is retired instead and the process survives if it has other
/// threads. A single-threaded program behaves as POSIX says; a multi-threaded
/// one loses the thread that took the signal rather than the whole program.
fn handle_default(signum: usize) {
    match default_action(signum) {
        DefaultAction::Terminate => scheduler::retire_me(),
        DefaultAction::Ignore => {}
    }
}

/// Calls a user-space signal handler.
///
/// The handler runs with its own signal blocked, and with the handler's
/// mask (`sa_mask`) applied on top of it, as POSIX requires.
fn run_handler(thread: &'static Thread, action: &SignalAction, signum: usize) {
    let mask = thread.signal_mask();
    let saved = mask.blocked();

    // POSIX: the signal being handled is blocked while the handler runs,
    // unless `SA_NODEFER` says otherwise. The handler's own mask is added
    // to the thread's mask for the duration.
    let mut effective = saved;
    if action.flags & super::posix::SA_NODEFER == 0 {
        effective |= bit(signum);
    }
    effective |= action.mask;
    mask.set_blocked(effective);

    // SAFETY: the handler address came from a `sigaction()` call, which is
    // the only way a user program can install one, and the kernel checks
    // that it is neither `SIG_DFL` nor `SIG_IGN` before getting here. The
    // call runs on the thread's own stack, in the same address space as the
    // program that installed it.
    let handler: extern "C" fn(core::ffi::c_int) =
        unsafe { core::mem::transmute(action.handler) };
    handler(signum as core::ffi::c_int);

    mask.set_blocked(saved);
}

/// The number of signals the kernel tracks, re-exported for convenience.
pub const SIGNAL_COUNT: usize = NSIG;

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn fatal_and_user_signals_terminate_by_default() {
        for signum in [
            sig::SIGINT,
            sig::SIGQUIT,
            sig::SIGABRT,
            sig::SIGTERM,
            sig::SIGKILL,
            sig::SIGUSR1,
            sig::SIGUSR2,
        ] {
            assert_eq!(default_action(signum), DefaultAction::Terminate);
        }
    }

    #[test]
    fn notification_and_job_control_signals_are_ignored_by_default() {
        for signum in [
            sig::SIGCHLD,
            sig::SIGCONT,
            sig::SIGURG,
            sig::SIGWINCH,
            sig::SIGSTOP,
            sig::SIGTSTP,
            sig::SIGTTIN,
            sig::SIGTTOU,
        ] {
            assert_eq!(default_action(signum), DefaultAction::Ignore);
        }
    }

    #[test]
    fn numbering_follows_the_c_library_not_linux() {
        // The numbers that differ between newlib and Linux. `libc` is no
        // help here even in principle: on the bare-metal target it does not
        // export these constants at all (`SIGCHLD`, `SIGCONT`, `SIGURG`,
        // `SIGSTOP` are behind its `unix` cfg), so the table has to spell
        // them out. Getting them from Linux's numbering instead would make
        // `SIGCHLD` (20) terminate a thread the way `SIGSEGV` (11) does.
        assert_eq!(sig::SIGURG, 16);
        assert_eq!(sig::SIGSTOP, 17);
        assert_eq!(sig::SIGTSTP, 18);
        assert_eq!(sig::SIGCONT, 19);
        assert_eq!(sig::SIGCHLD, 20);
        assert_eq!(sig::SIGUSR1, 30);
        assert_eq!(sig::SIGUSR2, 31);
    }
}
