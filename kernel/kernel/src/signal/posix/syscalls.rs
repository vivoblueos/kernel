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

//! The system-call side of the POSIX signal interfaces.
//!
//! Every function here follows the POSIX convention for the `sig*` family:
//! they return `0` on success and `-1` with `errno` set on failure, *except*
//! `sigwait()` and `sigtimedwait()`, which return the signal number directly.

use super::{
    apply_mask_op, bit, c_mask_to_kernel, sig, valid_signum, PosixSigAction, SignalAction, NSIG,
    SIG_BLOCK, SIG_DFL, SIG_ERR, SIG_IGN, SIG_SETMASK, SIG_UNBLOCK,
};
use crate::{process::current_process, scheduler, thread::Thread, types::Arc, vfs::uptr};
use blueos_infra::no_let_underscore::IgnoreResult;
use core::ffi::{c_int, c_void};
use libc::timespec;
use libc::sigset_t;

/// The `sigset_t` as the C side sees it: an `unsigned long`.
const SIGSET_BYTES: usize = core::mem::size_of::<u64>();

/// Largest structure copied to or from the caller by this module.
///
/// `struct sigaction` is 24 bytes, `timespec` 16 and newlib's `siginfo_t` 16 -
/// the cap only has to be an upper bound that keeps the stack buffer below it
/// finite.
const MAX_COPY: usize = 128;

/// The first page of the address space.
const NULL_PAGE: usize = 4096;

/// Whether a pointer into the first page is always invalid.
///
/// On a target with an MMU the null page is never mapped, so an argument that
/// lands there is a null-pointer nobody checked - `sigaction(sig, (void *)8,
/// NULL)` is the classic case - and reading it would fault in supervisor
/// context instead of reporting `EFAULT`.
///
/// The Cortex-M boards have no MMU and link the kernel at address zero
/// (`qemu_mps2_an385` puts FLASH at `ORIGIN = 0x0`), so there a low address is
/// an ordinary kernel address and must be copied as usual.
const NULL_PAGE_IS_UNMAPPED: bool = cfg!(any(target_arch = "riscv64", target_arch = "aarch64"));

/// Reads one `#[repr(C)]` value the caller passed in.
///
/// This is `copy_from_user`: the pointer belongs to the caller, so it is
/// copied through [`uptr`] rather than dereferenced. A user thread's pointer
/// is resolved through its page table (and demand-paged first), a kernel
/// thread's pointer is a kernel address and is copied directly. Anything that
/// cannot be read - a null page, an unmapped page, a structure larger than
/// [`MAX_COPY`] - is `EFAULT`, which is what POSIX asks for at this boundary.
fn copy_from_user<T: Copy>(ptr: *const T) -> Result<T, c_int> {
    let size = core::mem::size_of::<T>();
    if ptr.is_null()
        || (NULL_PAGE_IS_UNMAPPED && (ptr as usize) < NULL_PAGE)
        || size == 0
        || size > MAX_COPY
    {
        return Err(libc::EFAULT);
    }
    let mut buf = [0u8; MAX_COPY];
    uptr::read_bytes(ptr as *const u8, &mut buf[..size]).map_err(|_| libc::EFAULT)?;
    // SAFETY: `buf[..size]` was just filled with the caller's bytes, and
    // `read_unaligned` imposes no alignment requirement on the source.
    Ok(unsafe { core::ptr::read_unaligned(buf.as_ptr() as *const T) })
}

/// Writes one `#[repr(C)]` value back to the caller's buffer.
///
/// The `copy_to_user` counterpart of [`copy_from_user`], and it reports
/// `EFAULT` for the same reasons.
fn copy_to_user<T: Copy>(ptr: *mut T, val: &T) -> Result<(), c_int> {
    let size = core::mem::size_of::<T>();
    if ptr.is_null()
        || (NULL_PAGE_IS_UNMAPPED && (ptr as usize) < NULL_PAGE)
        || size == 0
        || size > MAX_COPY
    {
        return Err(libc::EFAULT);
    }
    // SAFETY: `val` points at a live, fully initialised `T`.
    let bytes = unsafe { core::slice::from_raw_parts(val as *const T as *const u8, size) };
    uptr::write_bytes(ptr as *mut u8, bytes).map_err(|_| libc::EFAULT)
}

/// Reads a C `sigset_t` (an `unsigned long`) into a kernel mask.
///
/// A null pointer is `EINVAL` rather than `EFAULT`: every one of these
/// interfaces accepts a null set to mean "no set" - `sigprocmask(SIG_SETMASK,
/// NULL, &old)` is the documented way to read the mask back - so only a
/// pointer that is meant to be read but cannot be is a fault.
fn read_c_mask(set: *const sigset_t) -> Result<usize, c_int> {
    if set.is_null() {
        return Err(libc::EINVAL);
    }
    // The C `sigset_t` is an `unsigned long`, which has the same width as a
    // pointer - so the value carries over unchanged. (`sigfillset()` sets
    // every bit, so the kernel has to accept a full mask rather than reject
    // the high half.)
    copy_from_user::<usize>(set as *const usize)
}

/// Writes a kernel mask back into a C `sigset_t`.
fn write_c_mask(set: *mut sigset_t, mask: usize) -> Result<(), c_int> {
    copy_to_user::<usize>(set as *mut usize, &mask)
}

/// POSIX `sigaction()`.
///
/// Installs a new disposition for `signum`, and reports the previous one
/// through `oact` when it is not null.
///
/// `act` points at a `struct sigaction` in the C layout described by
/// [`PosixSigAction`]. The `sa_handler` field carries either a user-space
/// function address or one of `SIG_DFL` / `SIG_IGN`.
pub fn sigaction(signum: c_int, act: *const c_void, oact: *mut c_void) -> c_int {
    if !valid_signum(signum) {
        return -libc::EINVAL;
    }
    // POSIX: an implementation cannot allow `SIGKILL` or `SIGSTOP` to be
    // caught or ignored, so their disposition cannot be changed at all -
    // even reporting the current one is refused, because no program can ever
    // have installed one.
    if signum as usize == sig::SIGKILL || signum as usize == sig::SIGSTOP {
        return -libc::EINVAL;
    }
    let Some(process) = current_process() else {
        // A thread that belongs to no process has no dispositions to
        // install into. This happens for kernel threads only.
        return -libc::EINVAL;
    };
    let signals = process.signals();

    // Read the new disposition before touching the table: a bad pointer must
    // leave the old disposition in place rather than install a half-read one.
    let new = if act.is_null() {
        None
    } else {
        match copy_from_user::<PosixSigAction>(act as *const PosixSigAction) {
            Ok(v) => Some(v),
            Err(errno) => return -errno,
        }
    };

    let old = signals.action(signum as usize);

    if let Some(new) = new {
        // `SIG_DFL` and `SIG_IGN` are the small non-zero values 0 and 1.
        // Everything else is a user-space address. A handler of `SIG_ERR`
        // (-1) is not a valid disposition.
        if new.sa_handler == SIG_ERR as usize {
            return -libc::EINVAL;
        }
        let disposition = SignalAction {
            handler: new.sa_handler,
            flags: new.sa_flags,
            mask: c_mask_to_kernel(new.sa_mask),
        };
        signals.set_action(signum as usize, disposition);
    }

    if !oact.is_null() {
        let previous = PosixSigAction {
            sa_handler: old.handler,
            sa_mask: old.mask,
            sa_flags: old.flags,
        };
        if let Err(errno) = copy_to_user::<PosixSigAction>(oact as *mut PosixSigAction, &previous) {
            return -errno;
        }
    }

    0
}

/// POSIX `sigprocmask()`.
///
/// Changes the calling thread's signal mask and reports the previous one
/// through `oldset`.
///
/// `set` may be null, in which case the mask is only reported.
pub fn sigprocmask(how: c_int, set: *const sigset_t, oldset: *mut sigset_t) -> c_int {
    if how != SIG_BLOCK && how != SIG_UNBLOCK && how != SIG_SETMASK {
        return -libc::EINVAL;
    }
    let thread = scheduler::current_thread();
    let mask = thread.signal_mask();
    let old = mask.blocked();

    if !set.is_null() {
        let requested = match read_c_mask(set) {
            Ok(m) => m,
            Err(errno) => return -errno,
        };
        let Some(new) = apply_mask_op(how, old, requested) else {
            return -libc::EINVAL;
        };
        mask.set_blocked(new);
        // Unblocking a signal that is already pending delivers it right
        // away: POSIX says the signal shall be delivered as soon as it is
        // no longer blocked, and nothing else would wake the thread.
        //
        // The test is on the bits that were actually cleared, not on the
        // numbers: a mask value going down does not mean a signal was
        // unblocked - `SIG_UNBLOCK` of a signal that was not blocked leaves
        // the value alone, and `SIG_SETMASK` can raise it.
        if old & !new != 0 {
            crate::signal::delivery::deliver_pending();
        }
    }

    if !oldset.is_null() {
        if let Err(errno) = write_c_mask(oldset, old) {
            return -errno;
        }
    }

    0
}

/// POSIX `sigpending()`.
///
/// Reports the set of signals that are pending for the calling thread, which
/// POSIX defines as the signals *raised while blocked*: an unblocked signal
/// is delivered at the next scheduling point and never observable here.
pub fn sigpending(set: *mut sigset_t) -> c_int {
    if set.is_null() {
        return -libc::EINVAL;
    }
    let thread = scheduler::current_thread();
    let blocked = thread.signal_mask().blocked();
    // The kernel's pending mask and the C `sigset_t` agree on the bit
    // positions - signal `n` is bit `n` in both - so no conversion is needed.
    //
    // The blocked mask is applied because a signal that is *not* blocked is
    // not pending in the POSIX sense: it is on its way to a handler. Every
    // implementation reports `pending & blocked`, and a caller that unblocked
    // a signal has already had it delivered by the time this returns.
    let pending = thread.pending_signals() as usize;
    if let Err(errno) = write_c_mask(set, pending & blocked) {
        return -errno;
    }
    0
}

/// The alternate signal stack of a thread.
///
/// The kernel does not run signal handlers on a separate stack yet, so
/// `sigaltstack()` records the request and reports it back, but the stack is
/// not actually used. Returning `ENOSYS` would be worse than accepting the
/// call: a caller that only *asks* for an alternate stack would then have to
/// treat every other failure as fatal.
pub fn sigaltstack(ss: *const c_void, old_ss: *mut c_void) -> c_int {
    if ss.is_null() && old_ss.is_null() {
        return -libc::EINVAL;
    }
    // The layout is newlib's: ss_sp (pointer), ss_flags (int), ss_size
    // (size_t). Reading the old value requires somewhere to keep it; the
    // kernel has no per-thread alternate stack yet, so report the default
    // (a disabled stack) instead of inventing state.
    if !old_ss.is_null() {
        #[repr(C)]
        #[derive(Clone, Copy)]
        struct SigAltStack {
            ss_sp: *mut c_void,
            ss_flags: c_int,
            ss_size: usize,
        }
        let empty = SigAltStack {
            ss_sp: core::ptr::null_mut(),
            ss_flags: 1, // SS_DISABLE
            ss_size: 0,
        };
        if let Err(errno) = copy_to_user::<SigAltStack>(old_ss as *mut SigAltStack, &empty) {
            return -errno;
        }
    }
    0
}

/// POSIX `sigsuspend()`.
///
/// Atomically replaces the calling thread's signal mask with `set` and waits
/// until a signal arrives.
///
/// Returns only when a handler for a signal that was pending runs, or when
/// the call is interrupted. The mask is restored to its previous value
/// before returning.
pub fn sigsuspend(set: *const sigset_t) -> c_int {
    let requested = match read_c_mask(set) {
        Ok(m) => m,
        Err(errno) => return -errno,
    };
    let thread = scheduler::current_thread();
    let mask = thread.signal_mask();
    let old = mask.blocked();
    mask.set_blocked(requested);

    // Wait until a signal that is not blocked by the new mask arrives. The
    // thread sleeps on its signal futex; `Thread::kill` wakes it.
    loop {
        if has_unblocked_signal(&thread, requested) {
            break;
        }
        let futex = thread.signal_futex();
        let observed = futex.load(core::sync::atomic::Ordering::Acquire);
        // Re-check after loading the futex value: a signal that arrived
        // between the two would otherwise be missed and the thread would
        // sleep again despite having a pending signal.
        if has_unblocked_signal(&thread, requested) {
            break;
        }
        crate::sync::atomic_wait::atomic_wait(futex, observed, crate::time::Tick::MAX)
            .ignore_result();
    }

    mask.set_blocked(old);
    0
}

/// Whether the thread has a pending signal that the given mask does not
/// block.
fn has_unblocked_signal(thread: &crate::thread::Thread, requested: usize) -> bool {
    thread.pending_signals() as usize & !requested != 0
}

/// POSIX `sigwait()`.
///
/// Waits for one of the signals in `set` to be delivered to the calling
/// thread, and returns that signal number.
///
/// Unlike `sigsuspend()`, `sigwait()` does not change the mask and does not
/// run the handler: it consumes the signal.
pub fn sigwait(set: *const sigset_t, sig: *mut c_int) -> c_int {
    if sig.is_null() {
        return -libc::EINVAL;
    }
    let wanted = match read_c_mask(set) {
        Ok(m) => m,
        Err(errno) => return -errno,
    };
    let thread = scheduler::current_thread();

    loop {
        if let Some(signum) = peek_wanted(&thread, wanted) {
            // Report the number first: a signal that has been taken out of the
            // pending set cannot be put back, so the caller's buffer has to be
            // known good before the signal is consumed.
            if let Err(errno) = copy_to_user::<c_int>(sig, &(signum as c_int)) {
                return -errno;
            }
            thread.clear_signal(signum as i32);
            return signum as c_int;
        }
        let futex = thread.signal_futex();
        let observed = futex.load(core::sync::atomic::Ordering::Acquire);
        if thread.pending_signals() as usize & wanted != 0 {
            continue;
        }
        crate::sync::atomic_wait::atomic_wait(futex, observed, crate::time::Tick::MAX)
            .ignore_result();
    }
}

/// POSIX `sigtimedwait()`.
///
/// Like `sigwait()`, but gives up after `timeout` and reports `EAGAIN`.
///
/// `timeout` is a *relative* interval, as POSIX specifies for this call (the
/// absolute-time rule belongs to `pselect()`). A null `timeout` means "wait
/// for as long as it takes", which is how `sigwaitinfo()` is built on top of
/// this call. A zero interval polls: the pending set is checked once and, if
/// nothing is there, the call returns `EAGAIN` without sleeping.
pub fn sigtimedwait(set: *const sigset_t, info: *mut c_void, timeout: *const timespec) -> c_int {
    let wanted = match read_c_mask(set) {
        Ok(m) => m,
        Err(errno) => return -errno,
    };
    let deadline = if timeout.is_null() {
        None
    } else {
        let ts = match copy_from_user::<timespec>(timeout) {
            Ok(ts) => ts,
            Err(errno) => return -errno,
        };
        if ts.tv_sec < 0 || ts.tv_nsec < 0 || ts.tv_nsec >= 1_000_000_000 {
            return -libc::EINVAL;
        }
        let span = ts.tv_sec as i64 * 1_000_000_000 + ts.tv_nsec as i64;
        Some(realtime_time_ns().saturating_add(span))
    };
    let thread = scheduler::current_thread();

    loop {
        if let Some(signum) = peek_wanted(&thread, wanted) {
            if !info.is_null() {
                if let Err(errno) = publish_siginfo(info, signum) {
                    return -errno;
                }
            }
            thread.clear_signal(signum as i32);
            return signum as c_int;
        }
        // Work out how long is left until the deadline. The remaining time
        // is what the futex wait is given; when it runs out the call reports
        // `EAGAIN`, which is the code POSIX assigns to "the timeout expired".
        let remaining = match deadline {
            None => i64::MAX,
            Some(deadline) => deadline - realtime_time_ns(),
        };
        if remaining <= 0 {
            return -libc::EAGAIN;
        }
        let millis = (remaining / 1_000_000).max(1) as u64;
        let futex = thread.signal_futex();
        let observed = futex.load(core::sync::atomic::Ordering::Acquire);
        if thread.pending_signals() as usize & wanted != 0 {
            continue;
        }
        crate::sync::atomic_wait::atomic_wait(
            futex,
            observed,
            crate::time::Tick::from_millis(millis),
        )
        .ignore_result();
    }
}

/// The `siginfo_t` as newlib lays it out.
///
/// newlib's `sys/signal.h` is not the Linux structure: it carries three
/// members only, and `si_code` follows `si_signo` directly.
///
/// ```text
/// offset 0: si_signo   (int)
/// offset 4: si_code    (int)
/// offset 8: si_value   (union sigval, pointer-sized)
/// total: 16 bytes
/// ```
///
/// Writing the Linux shape instead would put `si_code` where newlib expects
/// the signal number's neighbour and overrun the 16 bytes the caller
/// allocated. There is no `si_pid` here because newlib's structure has no
/// such member; a sender pid written past the end would be a stack overrun,
/// not a report.
#[repr(C)]
#[derive(Clone, Copy)]
struct PosixSiginfo {
    si_signo: c_int,
    si_code: c_int,
    si_value: usize,
}

/// `si_code` for a signal sent by a user process, as newlib numbers it.
const SI_USER: c_int = 1;

/// The lowest-numbered pending signal that is in `wanted`.
///
/// The signal is left pending: `sigwait()` and `sigtimedwait()` clear it only
/// after the caller's buffers have been written, so a bad pointer costs an
/// `EFAULT` rather than the signal.
fn peek_wanted(thread: &crate::thread::Thread, wanted: usize) -> Option<usize> {
    let ready = thread.pending_signals() as usize & wanted;
    if ready == 0 {
        return None;
    }
    (1..NSIG).find(|signum| ready & bit(*signum) != 0)
}

/// Fills in the `siginfo_t` for a signal taken by `sigwait()`.
fn publish_siginfo(info: *mut c_void, signum: usize) -> Result<(), c_int> {
    let details = PosixSiginfo {
        si_signo: signum as c_int,
        si_code: SI_USER,
        // `raise()` and `kill()` carry no value; only `sigqueue()` does, and
        // that path is not implemented.
        si_value: 0,
    };
    copy_to_user::<PosixSiginfo>(info as *mut PosixSiginfo, &details)
}

/// The current time on `CLOCK_REALTIME`, in nanoseconds.
fn realtime_time_ns() -> i64 {
    let mut ts = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // The kernel's clock numbering is used here: `CLOCK_REALTIME` is 0.
    if crate::syscall_handlers::posix_timers::clock_gettime(0, &mut ts) < 0 {
        return 0;
    }
    ts.tv_sec as i64 * 1_000_000_000 + ts.tv_nsec as i64
}
/// Sends `sig` to the process identified by `pid`. A `pid` of 0 means the
/// calling process, and `-1` means every process the caller may signal.
///
/// The kernel supports one process at a time in practice, so the delivery
/// targets the calling process.
pub fn kill(pid: libc::pid_t, sig: c_int) -> c_int {
    if !valid_signum(sig) {
        return -libc::EINVAL;
    }
    let Some(process) = current_process() else {
        return -libc::ESRCH;
    };
    if pid != 0 && pid != process.pid().0 as libc::pid_t {
        return -libc::ESRCH;
    }

    let mut delivered = 0;
    // The threads are cloned out of the process so that the wake can happen
    // after the lock is dropped. `for_each_thread()` holds the thread list
    // with interrupts disabled, and waking a sleeper asks the scheduler for a
    // re-schedule, which is not legal there.
    let mut waiters: alloc::vec::Vec<Arc<Thread>> = alloc::vec::Vec::new();
    process.for_each_thread(|thread| {
        let mut l = thread.lock();
        l.kill(sig);
        delivered += 1;
        // SAFETY: the process owns the thread, so it outlives this closure.
        waiters.push(unsafe { Arc::clone_from(thread) });
    });
    if delivered == 0 {
        return -libc::ESRCH;
    }
    // A thread asleep in `sigsuspend()` or `sigwait()` has to be woken,
    // otherwise the signal would sit in the pending set until the next
    // unrelated wake-up.
    for thread in &waiters {
        thread.wake_signal_waiters();
    }
    // Deliver to the calling thread right away, the same way `raise()`
    // does. The other threads of the process pick the signal up at their
    // next scheduling point.
    crate::signal::delivery::deliver_pending();
    // And a thread asleep in `poll()` has to come back with `EINTR` rather
    // than wait out its timeout. This is done here, outside the thread locks
    // the loop above took, because waking a waiter is not legal from inside
    // a critical section.
    crate::thread::bump_poll_epoch();
    0
}

/// POSIX `raise()`.
///
/// Sends `sig` to the calling thread.
///
/// POSIX requires the signal to have been delivered when the function
/// returns, so the thread yields once: the scheduler's signal check runs
/// on the way back and hands the signal to its handler.
pub fn raise(sig: c_int) -> c_int {
    if !valid_signum(sig) {
        return -libc::EINVAL;
    }
    let thread = scheduler::current_thread();
    {
        let mut l = thread.lock();
        l.kill(sig);
    }
    // A no-op for the caller, which is running rather than waiting, but the
    // wake is what `sigsuspend()`/`sigwait()` on this thread would need.
    thread.wake_signal_waiters();
    // POSIX requires the signal to have been delivered when the function
    // returns. The scheduler's signal check only runs at a context switch,
    // and a switch does not necessarily happen - when the thread is the only
    // runnable one, `yield_me()` returns without switching. So the delivery
    // is done here, and the yield is only there to give the other threads a
    // chance to run.
    crate::signal::delivery::deliver_pending();
    // The thread lock is released by now, so waking pollers is legal. The
    // signal was raised on this thread, which is running rather than waiting,
    // but the same call is what a signal aimed at another thread uses - see
    // `kill()` above - so the wake is unconditional.
    crate::thread::bump_poll_epoch();
    scheduler::yield_me();
    0
}

/// The number of bytes a C `sigset_t` occupies, for the ABI check.
pub const CSIGSET_SIZE: usize = SIGSET_BYTES;
