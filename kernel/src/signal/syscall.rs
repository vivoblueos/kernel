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

// Kernel-side signal syscalls (minimal POSIX subset).
//
// Notes:
// - Currently treats "pid" as a thread id (TID).
// - Only standard signals 1..31 are supported (NSIG=32).
// - Real-time delivery/queueing is not supported; we keep at most one siginfo
//   slot per signal per thread.

use crate::{
    arch, scheduler,
    thread::{self, GlobalQueueVisitor, KernelSigAction, SigAltStack, SigInfo, Thread, ThreadNode},
    time,
    time::WAITING_FOREVER,
};
use libc::{c_int, c_void, pid_t, sighandler_t, sigset_t, timespec};

// Kernel internal representation for per-thread signal masks.
// We keep 32 bits: POSIX signal N corresponds to bit (N-1).
type SigMask = u32;

#[inline]
fn sigset_to_mask(set: sigset_t) -> SigMask {
    // Only preserve signals 1..31; bit 31 (signal 32) is unused with NSIG=32.
    let mut v: SigMask = 0;
    unsafe {
        core::ptr::copy_nonoverlapping(
            (&set as *const sigset_t).cast::<u8>(),
            (&mut v as *mut SigMask).cast::<u8>(),
            core::mem::size_of::<SigMask>().min(core::mem::size_of::<sigset_t>()),
        );
    }
    v & 0x7FFF_FFFF
}

#[inline]
fn mask_to_sigset(mask: SigMask) -> sigset_t {
    let mut out: sigset_t = unsafe { core::mem::zeroed() };
    unsafe {
        core::ptr::copy_nonoverlapping(
            (&mask as *const SigMask).cast::<u8>(),
            (&mut out as *mut sigset_t).cast::<u8>(),
            core::mem::size_of::<SigMask>().min(core::mem::size_of::<sigset_t>()),
        );
    }
    out
}

// Types must match the userspace layout used by `libc` and the syscall handler.
#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone, Copy)]
pub struct sigaltstack {
    pub ss_sp: *mut c_void,
    pub ss_flags: c_int,
    pub ss_size: usize,
}

impl Default for sigaltstack {
    fn default() -> Self {
        Self {
            ss_sp: core::ptr::null_mut(),
            ss_flags: 0,
            ss_size: 0,
        }
    }
}

#[allow(non_camel_case_types)]
#[repr(align(8))]
#[derive(Clone, Copy, Default)]
pub struct siginfo_t {
    pub si_signo: c_int,
    pub si_errno: c_int,
    pub si_code: c_int,
    _pad: [c_int; 29],
    _align: [usize; 0],
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Default)]
pub struct sigaction {
    pub sa_sigaction: sighandler_t,
    pub sa_mask: sigset_t,
    pub sa_flags: c_int,
    pub sa_restorer: Option<extern "C" fn()>,
}

#[inline]
fn handler_to_sighandler_t(h: Option<extern "C" fn(c_int)>) -> sighandler_t {
    match h {
        core::option::Option::None => libc::SIG_DFL as sighandler_t,
        Some(f) => f as usize as sighandler_t,
    }
}

#[inline]
fn sighandler_t_to_handler(v: sighandler_t) -> Option<extern "C" fn(c_int)> {
    if v == libc::SIG_DFL as sighandler_t {
        None
    } else if v == libc::SIG_IGN as sighandler_t {
        // Kernel currently doesn't model SIG_IGN distinctly; treat as default.
        None
    } else if v == libc::SIG_ERR as sighandler_t {
        None
    } else {
        Some(unsafe { core::mem::transmute::<usize, extern "C" fn(c_int)>(v as usize) })
    }
}

#[inline]
fn validate_signum(signum: c_int) -> Result<usize, c_int> {
    if signum <= 0 || signum >= 32 {
        return Err(-libc::EINVAL);
    }
    Ok(signum as usize)
}

// pid_t type lookups
fn find_thread_by_tid(tid: pid_t) -> Option<ThreadNode> {
    if tid <= 0 {
        return None;
    }
    let target = tid as u32;
    let mut it = GlobalQueueVisitor::new();
    while let Some(t) = it.next() {
        if Thread::tid(&t) == target {
            return Some(t);
        }
    }
    None
}

#[inline]
fn sigset_bit_for(signum: usize) -> sigset_t {
    // POSIX numbering: signal N is bit (N-1).
    mask_to_sigset(1u32 << ((signum - 1) as u32))
}

#[inline]
fn take_pending_from_set(t: &mut Thread, set: sigset_t) -> Option<(c_int, SigInfo)> {
    let pending = t.pending_signals();
    let set_mask = sigset_to_mask(set);
    for signum in 1..32 {
        let bit = 1u32 << signum;
        if pending & bit == 0 {
            continue;
        }
        let mask = 1u32 << ((signum - 1) as u32);
        if set_mask & mask == 0 {
            continue;
        }
        t.clear_signal(signum as i32);
        let info = t.take_siginfo(signum as i32).unwrap_or(SigInfo {
            si_signo: signum as i32,
            si_errno: 0,
            si_code: 0,
        });
        return Some((signum as c_int, info));
    }
    None
}

fn deliver_to_tid(tid: pid_t, sig: c_int, info: *mut siginfo_t) -> c_int {
    let signum = match validate_signum(sig) {
        Ok(v) => v as i32,
        Err(e) => return e,
    };

    let Some(target) = find_thread_by_tid(tid) else {
        return -libc::ESRCH;
    };

    let sinfo = if info.is_null() {
        SigInfo {
            si_signo: signum,
            si_errno: 0,
            si_code: 0,
        }
    } else {
        let u = unsafe { &*(info as *const siginfo_t) };
        SigInfo {
            si_signo: u.si_signo,
            si_errno: u.si_errno,
            si_code: u.si_code,
        }
    };

    target.lock().push_siginfo(signum, sinfo);

    // Fast path for self-signal: we need a guaranteed
    // context switch so `prepare_signal_handling()` runs
    if Thread::id(&target) == scheduler::current_thread_id() {
        scheduler::yield_me_definitely();
        return 0;
    }

    //FIXME: we must implement correct wakeup, should add a waitqueue for signal waiters
    let st = target.state();
    if st == thread::SUSPENDED {
        let _ = scheduler::queue_ready_thread(thread::SUSPENDED, target);
    }
    // UP: give scheduler a hint to reschedule soon
    scheduler::yield_me_now_or_later();
    // SMP: Ensure the scheduler re-checks runnable threads soon.
    if blueos_kconfig::CONFIG_NUM_CORES > 1 {
        arch::send_reschedule_ipi_all();
    }
    0
}

pub fn sigaction(signum: c_int, act: *const c_void, oact: *mut c_void) -> c_int {
    let signum: c_int = match validate_signum(signum) {
        Ok(v) => v as c_int,
        Err(e) => return e,
    };
    let current = scheduler::current_thread();

    // Copy out old action if requested.
    if !oact.is_null() {
        let old = {
            let l = current.lock();
            l.get_sigaction(signum)
        };
        let out = sigaction {
            sa_sigaction: handler_to_sighandler_t(old.sa_handler),
            sa_mask: old.sa_mask,
            sa_flags: old.sa_flags as c_int,
            sa_restorer: None,
        };
        unsafe { (oact as *mut c_void).cast::<sigaction>().write(out) };
    }

    if act.is_null() {
        return 0;
    }

    let new_act = unsafe { &*(act as *const c_void).cast::<sigaction>() };
    let sa = KernelSigAction {
        sa_handler: sighandler_t_to_handler(new_act.sa_sigaction),
        sa_flags: new_act.sa_flags as usize,
        sa_mask: new_act.sa_mask,
    };
    current.lock().set_sigaction(signum, sa);
    0
}

pub fn sigaltstack(ss: *const c_void, old_ss: *mut c_void) -> c_int {
    let current = scheduler::current_thread();
    if !old_ss.is_null() {
        let old = current.lock().get_sigaltstack();
        let out = sigaltstack {
            ss_sp: old.ss_sp as *mut core::ffi::c_void as *mut c_void,
            ss_flags: old.ss_flags,
            ss_size: old.ss_size,
        };
        unsafe { (old_ss as *mut c_void).cast::<sigaltstack>().write(out) };
    }

    if ss.is_null() {
        return 0;
    }

    let new_ss = unsafe { &*(ss as *const c_void).cast::<sigaltstack>() };
    let kss = SigAltStack {
        ss_sp: new_ss.ss_sp as *mut c_void as *mut core::ffi::c_void,
        ss_flags: new_ss.ss_flags,
        ss_size: new_ss.ss_size,
    };
    current.lock().set_sigaltstack(kss);
    0
}

pub fn sigpending(set: *mut sigset_t) -> c_int {
    if set.is_null() {
        return -libc::EINVAL;
    }
    let current = scheduler::current_thread();
    let pending = current.lock().pending_signals();
    let mut out: sigset_t = 0;
    for signum in 1..32 {
        if pending & (1 << signum) != 0 {
            out |= sigset_bit_for(signum);
        }
    }
    unsafe { set.write(out) };
    0
}

pub fn sigprocmask(how: c_int, set: *const sigset_t, oldset: *mut sigset_t) -> c_int {
    let current = scheduler::current_thread();
    let mut l = current.lock();

    if !oldset.is_null() {
        unsafe { oldset.write(mask_to_sigset(l.signal_mask())) };
    }

    if set.is_null() {
        return 0;
    }
    let mut new_mask = sigset_to_mask(unsafe { *set });
    // SIGKILL and SIGSTOP aren't able to block
    new_mask &= !(1u32 << ((libc::SIGKILL - 1) as u32));
    new_mask &= !(1u32 << ((libc::SIGSTOP - 1) as u32));
    match how {
        libc::SIG_BLOCK => {
            let cur = l.signal_mask();
            l.set_signal_mask(cur | new_mask);
        }
        libc::SIG_UNBLOCK => {
            let cur = l.signal_mask();
            l.set_signal_mask(cur & !new_mask);
        }
        libc::SIG_SETMASK => {
            l.set_signal_mask(new_mask);
        }
        _ => return -libc::EINVAL,
    }

    // If unblocking made some pending signals deliverable, ensure they are
    if l.has_pending_signals() {
        drop(l);
        scheduler::yield_me_definitely();
    }

    0
}

pub fn sigqueueinfo(pid: pid_t, sig: c_int, info: *mut siginfo_t) -> c_int {
    deliver_to_tid(pid, sig, info)
}

pub fn sigsuspend(set: *const sigset_t) -> c_int {
    if set.is_null() {
        return -libc::EINVAL;
    }
    // POSIX: SIGKILL and SIGSTOP are not blockable; ignore them in the supplied mask.
    let mut new_mask = sigset_to_mask(unsafe { *set });
    new_mask &= !(1u32 << ((libc::SIGKILL - 1) as u32));
    new_mask &= !(1u32 << ((libc::SIGSTOP - 1) as u32));
    let t = scheduler::current_thread();
    {
        let mut l = t.lock();
        l.save_signal_mask();
        l.set_signal_mask(new_mask);
    }

    // Sleep until woken by a signal delivery (or some other event).
    // POSIX behavior: sigsuspend returns -1/EINTR after a signal handler runs.
    scheduler::suspend_me_for(WAITING_FOREVER);

    // Restore mask and return EINTR (POSIX behavior).
    {
        let mut l = t.lock();
        l.restore_saved_signal_mask();
    }
    -libc::EINTR
}

pub fn sigtimedwait(set: *const sigset_t, info: *mut c_void, timeout: *const timespec) -> c_int {
    if set.is_null() {
        return -libc::EINVAL;
    }
    let mut set = sigset_to_mask(unsafe { *set });
    // POSIX: SIGKILL and SIGSTOP are not waitable; ignore them in the supplied mask.
    set &= !(1u32 << ((libc::SIGKILL - 1) as u32));
    set &= !(1u32 << ((libc::SIGSTOP - 1) as u32));
    let timeout_ticks = if timeout.is_null() {
        None
    } else {
        let ts = unsafe { &*timeout };
        let ms = (ts.tv_sec as i64)
            .saturating_mul(1000)
            .saturating_add((ts.tv_nsec as i64) / 1_000_000);
        Some(time::tick_from_millisecond(ms.max(0) as usize))
    };

    let t = scheduler::current_thread();
    let old_mask = { t.lock().signal_mask() };
    {
        let mut l = t.lock();
        let cur = l.signal_mask();
        l.set_signal_mask(cur | set);
    }

    loop {
        // If we already have a pending matching signal, consume it immediately.
        let maybe = {
            let mut l = t.lock();
            take_pending_from_set(&mut l, mask_to_sigset(set))
        };
        if let Some((signo, sinfo)) = maybe {
            if !info.is_null() {
                let out = siginfo_t {
                    si_signo: sinfo.si_signo as c_int,
                    si_errno: sinfo.si_errno as c_int,
                    si_code: sinfo.si_code as c_int,
                    ..Default::default()
                };
                unsafe { (info as *mut c_void).cast::<siginfo_t>().write(out) };
            }
            // Restore mask before returning.
            {
                let mut l = t.lock();
                l.set_signal_mask(old_mask);
            }
            return signo;
        }

        // Otherwise, sleep until a matching signal arrives or until the timeout.
        match timeout_ticks {
            Some(ticks) => {
                scheduler::suspend_me_for(ticks.max(1));
                // After waking (either due to signal delivery or timer), loop
                // again to check pending signals. If nothing is available, we
                // treat it as a timeout.
                let maybe_after = {
                    let mut l = t.lock();
                    take_pending_from_set(&mut l, mask_to_sigset(set))
                };
                if let Some((signo, sinfo)) = maybe_after {
                    if !info.is_null() {
                        let out = siginfo_t {
                            si_signo: sinfo.si_signo as c_int,
                            si_errno: sinfo.si_errno as c_int,
                            si_code: sinfo.si_code as c_int,
                            ..Default::default()
                        };
                        unsafe { (info as *mut c_void).cast::<siginfo_t>().write(out) };
                    }
                    {
                        let mut l = t.lock();
                        l.set_signal_mask(old_mask);
                    }
                    return signo;
                }
                {
                    let mut l = t.lock();
                    l.set_signal_mask(old_mask);
                }
                return -libc::EAGAIN;
            }
            None => {
                scheduler::suspend_me_for(WAITING_FOREVER);
            }
        }
    }
}

// all use *deliver_to_tid*, when implement multi-threaded process support, need change here.
pub fn kill(pid: pid_t, sig: c_int) -> c_int {
    if pid <= 0 {
        return -libc::ESRCH;
    }
    deliver_to_tid(pid, sig, core::ptr::null_mut())
}

pub fn tgkill(_tgid: pid_t, pid: pid_t, sig: c_int) -> c_int {
    if pid <= 0 {
        return -libc::ESRCH;
    }
    deliver_to_tid(pid, sig, core::ptr::null_mut())
}

pub fn tkill(pid: pid_t, sig: c_int) -> c_int {
    if pid <= 0 {
        return -libc::ESRCH;
    }
    deliver_to_tid(pid, sig, core::ptr::null_mut())
}
