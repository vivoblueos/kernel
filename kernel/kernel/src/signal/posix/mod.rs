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

//! POSIX signal dispositions, per-thread masks and delivery.
//!
//! The kernel already had a *kernel-internal* signal mechanism: a thread can
//! be handed a Rust closure to run when a signal arrives (see
//! `Thread::kill_with_once_handler`), and `signal::handle_signals` runs it at
//! the next scheduling point. That mechanism is fine for the kernel's own
//! use - `SIGTERM` shuts a thread down - but it cannot express what POSIX
//! asks for:
//!
//! * `sigaction()` installs a *user-space* handler, and the kernel must call
//!   that address with the signal number as its argument.
//! * `sigprocmask()` blocks signals per thread, and a blocked signal stays
//!   pending until it is unblocked.
//! * `sigpending()` reports the pending set.
//! * `sigsuspend()` atomically replaces the mask and waits.
//!
//! This module adds the state POSIX needs and routes delivery through it.
//!
//! # Numbering
//!
//! Signal numbers are 1-based (`SIGINT` is 2), which is what both newlib and
//! the kernel's `signal/consts.rs` use. The bitmaps use bit `signum` itself,
//! not `signum - 1`: newlib spells `sigaddset()` as the macro
//! `(*(what) |= (1 << (sig)), 0)`, and a `sigset_t` crosses the syscall
//! boundary unchanged, so a bit map that shifted by one would silently move
//! every signal one number up. `SIGUSR1` is 30 in newlib, so its bit is
//! `1 << 30`. Bit 0 is therefore unused, which is why `NSIG` counts the
//! signals *and* the hole at zero.
//!
//! # Where the state lives
//!
//! * The *disposition* (`sigaction`) is a per-process property in POSIX, and
//!   is stored in [`ProcessSignalState`].
//! * The *mask* and the *pending set* are per-thread, and live in the
//!   thread's existing `SignalContext`.
//!
//! # Delivery
//!
//! When the kernel has a pending signal for a thread, [`take_pending`]
//! returns the lowest-numbered signal that is neither blocked nor
//! `SIG_IGN`-ed, having also cleared the pending bit. The caller then
//! arranges for the user-space handler to run.

use crate::{process::Process, thread::Thread};
use core::ffi::c_int;
use crate::sync::SpinLock;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};

pub mod syscalls;

/// The signal numbers, as the C library spells them.
///
/// These are newlib's numbers, not Linux's, and not the ones in the `libc`
/// crate. The programs that reach these syscalls are compiled against newlib,
/// and its `<signal.h>` puts several of the job-control and notification
/// signals in different slots than Linux does:
///
/// | signal      | newlib | Linux |
/// |-------------|--------|-------|
/// | `SIGURG`    | 16     | 23    |
/// | `SIGSTOP`   | 17     | 19    |
/// | `SIGTSTP`   | 18     | 20    |
/// | `SIGCONT`   | 19     | 18    |
/// | `SIGCHLD`   | 20     | 17    |
///
/// Only the numbers both agree on - `SIGINT`, `SIGQUIT`, `SIGABRT`,
/// `SIGTERM`, `SIGWINCH` - would silently work if `libc`'s constants were
/// used, so the table below is spelled out instead.
pub mod sig {
    pub const SIGHUP: usize = 1;
    pub const SIGINT: usize = 2;
    pub const SIGQUIT: usize = 3;
    pub const SIGILL: usize = 4;
    pub const SIGTRAP: usize = 5;
    pub const SIGABRT: usize = 6;
    pub const SIGEMT: usize = 7;
    pub const SIGFPE: usize = 8;
    pub const SIGKILL: usize = 9;
    pub const SIGBUS: usize = 10;
    pub const SIGSEGV: usize = 11;
    pub const SIGSYS: usize = 12;
    pub const SIGPIPE: usize = 13;
    pub const SIGALRM: usize = 14;
    pub const SIGTERM: usize = 15;
    pub const SIGURG: usize = 16;
    pub const SIGSTOP: usize = 17;
    pub const SIGTSTP: usize = 18;
    pub const SIGCONT: usize = 19;
    pub const SIGCHLD: usize = 20;
    pub const SIGTTIN: usize = 21;
    pub const SIGTTOU: usize = 22;
    pub const SIGIO: usize = 23;
    pub const SIGXCPU: usize = 24;
    pub const SIGXFSZ: usize = 25;
    pub const SIGVTALRM: usize = 26;
    pub const SIGPROF: usize = 27;
    pub const SIGWINCH: usize = 28;
    pub const SIGPWR: usize = 29;
    pub const SIGUSR1: usize = 30;
    pub const SIGUSR2: usize = 31;
}

/// The number of signals the kernel tracks.
///
/// newlib defines `NSIG` as 32 ("signal 0 implied"), so the usable signal
/// numbers are 1..=31 and `NSIG` itself is not a signal. The pending set is
/// a `u32` and a signal lives in bit `signum` (see [`bit`]), so the table
/// covers the whole bitmap exactly: signal 31 is the highest bit.
///
/// A signal number is valid when `1 <= signum < NSIG`; see
/// [`valid_signum`].
pub const NSIG: usize = 32;

// The pending set is an `AtomicU32` and the once-handler table is indexed by
// the signal number, so `NSIG` cannot grow past the bitmap width without
// changing both.
const _: () = assert!(NSIG <= 32);

/// Whether `signum` names a signal this kernel can carry.
///
/// `0` is not a signal: it is what `kill()` uses to mean "my process group".
/// `NSIG` is the count of signals, not a signal number. Everything outside
/// `1..NSIG` is `EINVAL` at the syscall boundary.
pub const fn valid_signum(signum: c_int) -> bool {
    signum > 0 && (signum as usize) < NSIG
}

/// `SIG_DFL` - the default disposition (terminate the thread).
pub const SIG_DFL: usize = 0;
/// `SIG_IGN` - ignore the signal.
pub const SIG_IGN: usize = 1;
/// `SIG_ERR` - returned by `signal()` when the disposition could not be set.
pub const SIG_ERR: isize = -1;

/// `sa_flags` bit: the handler restarts interrupted syscalls.
pub const SA_RESTART: c_int = 0x1000_0000;
/// `sa_flags` bit: do not add the signal itself to the handler's mask.
pub const SA_NODEFER: c_int = 0x4000_0000;
/// `sa_flags` bit: the signal is delivered on an alternate stack.
pub const SA_ONSTACK: c_int = 0x0800_0000;
/// `sa_flags` bit: the handler takes three arguments (`sig`, `siginfo`,
/// `ucontext`).
pub const SA_SIGINFO: c_int = 0x0000_0004;

/// `sigprocmask()`: add the signals in `set` to the mask.
///
/// The values are newlib's, not POSIX's. newlib's `sys/signal.h` defines
/// `SIG_SETMASK` as 0, `SIG_BLOCK` as 1 and `SIG_UNBLOCK` as 2, while POSIX
/// numbers them 2, 0 and 1. A C caller passes the newlib value straight
/// through, so the kernel has to use the same numbering - otherwise
/// `sigprocmask(SIG_SETMASK, ...)` would be taken for a `SIG_BLOCK` and
/// block the signals instead of replacing the mask.
pub const SIG_SETMASK: c_int = 0;
pub const SIG_BLOCK: c_int = 1;
pub const SIG_UNBLOCK: c_int = 2;

/// The disposition of one signal.
///
/// `handler` holds the *user-space* address of the handler function, or one
/// of [`SIG_DFL`] / [`SIG_IGN`]. It is stored as a `usize` rather than a
/// function pointer because the value comes from the user and is never
/// called from the kernel directly - it is jumped to from a signal frame.
#[derive(Clone, Copy)]
pub struct SignalAction {
    pub handler: usize,
    pub flags: c_int,
    /// The mask that is in effect while the handler runs.
    pub mask: usize,
}

impl Default for SignalAction {
    fn default() -> Self {
        Self {
            handler: SIG_DFL,
            flags: 0,
            mask: 0,
        }
    }
}

/// The per-process signal dispositions.
#[derive(Default)]
pub struct ProcessSignalState {
    actions: [SignalAction; NSIG],
}

impl ProcessSignalState {
    /// Reads the disposition of `signum` (1-based).
    pub fn action(&self, signum: usize) -> SignalAction {
        if signum == 0 || signum >= NSIG {
            return SignalAction::default();
        }
        self.actions[signum - 1]
    }

    /// Replaces the disposition of `signum` (1-based) and returns the old one.
    pub fn set_action(&mut self, signum: usize, action: SignalAction) -> SignalAction {
        if signum == 0 || signum >= NSIG {
            return SignalAction::default();
        }
        core::mem::replace(&mut self.actions[signum - 1], action)
    }
}

/// The signal state of one process.
///
/// Kept behind a [`SpinLock`] because `sigaction()` may be called from any
/// thread of the process while another thread is delivering a signal.
pub struct ProcessSignals {
    state: SpinLock<ProcessSignalState>,
}

impl Default for ProcessSignals {
    fn default() -> Self {
        Self {
            state: SpinLock::new(ProcessSignalState::default()),
        }
    }
}

impl ProcessSignals {
    pub fn action(&self, signum: usize) -> SignalAction {
        self.state.irqsave_lock().action(signum)
    }

    pub fn set_action(&self, signum: usize, action: SignalAction) -> SignalAction {
        self.state.irqsave_lock().set_action(signum, action)
    }
}

/// The per-thread signal mask.
///
/// A plain atomic is enough: the mask is read and written with a single
/// load/store, and POSIX does not require the read-modify-write of
/// `sigprocmask()` to be atomic with respect to other threads.
pub struct ThreadSignalMask {
    // The mask is as wide as a pointer, which is also the width of the C
    // `sigset_t` (an `unsigned long`). A 32-bit target has no 64-bit atomic
    // operations, so the width has to follow the pointer.
    blocked: AtomicUsize,
}

impl ThreadSignalMask {
    /// Creates an empty mask.
    ///
    /// `const` because a `Thread` has to be constructible in a const context.
    pub const fn new() -> Self {
        Self {
            blocked: AtomicUsize::new(0),
        }
    }
}

impl Default for ThreadSignalMask {
    fn default() -> Self {
        Self::new()
    }
}

impl core::fmt::Debug for ThreadSignalMask {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ThreadSignalMask")
            .field("blocked", &self.blocked())
            .finish()
    }
}

impl ThreadSignalMask {
    pub fn blocked(&self) -> usize {
        self.blocked.load(Ordering::Acquire)
    }

    pub fn set_blocked(&self, mask: usize) {
        self.blocked.store(mask, Ordering::Release);
    }
}

/// Converts a 1-based signal number into a bitmap bit.
///
/// Signal `n` lives in bit `n`, which is the numbering newlib's `sigset_t`
/// uses: `sigaddset()` is the macro `(*(what) |= (1 << (sig)), 0)` and
/// `sigismember()` is `(((*(what)) & (1<<(sig))) != 0)`. The kernel keeps the
/// same bit positions so that a set built by the C library needs no
/// conversion on the way in or out - and so that `SIGUSR1` (30 in newlib)
/// cannot be mistaken for `SIGUSR2` (31). Bit 0 is unused because signal 0
/// does not exist.
pub const fn bit(signum: usize) -> usize {
    1usize << signum
}

/// Applies the `sigprocmask()` `how` operation to `old`, yielding the new
/// mask.
pub fn apply_mask_op(how: c_int, old: usize, set: usize) -> Option<usize> {
    match how {
        SIG_BLOCK => Some(old | set),
        SIG_UNBLOCK => Some(old & !set),
        SIG_SETMASK => Some(set),
        _ => None,
    }
}

/// Picks the signal that should be delivered next to `thread`.
///
/// Returns the 1-based signal number, or `None` when nothing is pending.
///
/// A signal is skipped when it is blocked by the thread's mask, or when its
/// disposition is `SIG_IGN` (an ignored signal is discarded rather than
/// left pending forever). The pending bit of the chosen signal is cleared
/// before returning, so the caller owns it.
pub fn take_pending(thread: &Thread, process: Option<&Process>) -> Option<usize> {
    let pending = thread.pending_signals();
    if pending == 0 {
        return None;
    }
    let blocked = thread.signal_mask().blocked();
    let process_signals = process.map(|p| p.signals());

    for signum in 1..NSIG {
        let flag = bit(signum);
        if pending as usize & flag == 0 {
            continue;
        }
        if blocked & flag != 0 {
            // Blocked: leave the signal pending.
            continue;
        }
        if let Some(signals) = process_signals {
            let action = signals.action(signum);
            if action.handler == SIG_IGN {
                // Ignored: discard it.
                thread.clear_signal(signum as i32);
                continue;
            }
        }
        thread.clear_signal(signum as i32);
        return Some(signum);
    }
    None
}

/// The signals that are pending but blocked, as a bitmap.
pub fn pending_mask(thread: &Thread) -> usize {
    thread.pending_signals() as usize
}

/// The list of signals a thread is currently blocking.
pub fn blocked_signals(thread: &Thread) -> Vec<usize> {
    let blocked = thread.signal_mask().blocked();
    (1..NSIG)
        .filter(|signum| blocked & bit(*signum) != 0)
        .collect()
}

/// The `struct sigaction` as newlib lays it out.
///
/// The C caller allocates this type and hands the kernel a pointer to it, so
/// the kernel must read exactly the bytes newlib wrote. Measured on a
/// 64-bit target with newlib's `signal.h`:
///
/// ```text
/// offset  0: sa_handler  (8 bytes, a function pointer or SIG_DFL/SIG_IGN)
/// offset  8: sa_mask     (8 bytes, sigset_t == unsigned long)
/// offset 16: sa_flags    (4 bytes)
/// offset 20: padding
/// total: 24 bytes
/// ```
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PosixSigAction {
    pub sa_handler: usize,
    pub sa_mask: usize,
    pub sa_flags: c_int,
}

/// Converts a C `sigset_t` (an `unsigned long`) into the kernel's mask.
///
/// The two have the same width - both follow the pointer width - so this is
/// the identity. It stays a function so that the conversion is in one place
/// if the widths ever differ.
pub fn c_mask_to_kernel(mask: usize) -> usize {
    mask
}

impl Default for PosixSigAction {
    fn default() -> Self {
        Self {
            sa_handler: SIG_DFL,
            sa_mask: 0,
            sa_flags: 0,
        }
    }
}
