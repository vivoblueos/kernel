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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

use super::errno::ERRNO;
use blueos_header::syscalls::NR::{
    RtSigAction, RtSigPending, RtSigProcmask, RtSigQueueInfo, RtSigSuspend, RtSigTimedWait,
    SigAltStack,
};
use blueos_scal::bk_syscall;
use core::{mem, ptr};
use libc::{c_int, c_ulong, c_void, pid_t, sigset_t, sigval, size_t, timespec};
pub mod consts;
pub use consts::*;

type SigSet = u64;

pub(crate) const SIG_DFL: usize = 0;
pub(crate) const SIG_IGN: usize = 1;
pub(crate) const SIG_ERR: isize = -1;
pub(crate) const SIG_HOLD: isize = 2;

// use linux constants now
pub const SA_RESTART: usize = 0x1000_0000;

#[repr(C)]
#[derive(Clone)]
#[allow(non_camel_case_types)]
pub struct sigaltstack {
    pub ss_sp: *mut c_void,
    pub ss_flags: c_int,
    pub ss_size: size_t,
}

/// copy from libc
#[repr(align(8))]
#[allow(non_camel_case_types)]
pub struct siginfo_t {
    pub si_signo: c_int,
    pub si_errno: c_int,
    pub si_code: c_int,
    _pad: [c_int; 29],
    _align: [usize; 0],
}

#[allow(non_camel_case_types)]
pub struct sigaction {
    pub sa_handler: Option<extern "C" fn(c_int)>,
    pub sa_flags: c_ulong,
    pub sa_restorer: Option<unsafe extern "C" fn()>,
    pub sa_mask: sigset_t,
}

#[no_mangle]
pub unsafe extern "C" fn sigaction(
    sig: c_int,
    act: *const sigaction,
    oact: *mut sigaction,
) -> c_int {
    bk_syscall!(RtSigAction, sig, act as *const c_void, oact as *mut c_void) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigaddset(set: *mut sigset_t, signo: c_int) -> c_int {
    if signo <= 0 || signo as usize > NSIG.max(SIGRTMAX) {
        ERRNO.set(libc::EINVAL);
        return -1;
    }

    if let Some(set) = unsafe { (set as *mut SigSet).as_mut() } {
        *set |= 1 << (signo as usize - 1);
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn sigaltstack(ss: *const sigaltstack, old_ss: *mut sigaltstack) -> c_int {
    bk_syscall!(SigAltStack, ss as *const c_void, old_ss as *mut c_void) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigdelset(set: *mut sigset_t, signo: c_int) -> c_int {
    if signo <= 0 || signo as usize > NSIG.max(SIGRTMAX) {
        ERRNO.set(libc::EINVAL);
        return -1;
    }

    if let Some(set) = unsafe { (set as *mut SigSet).as_mut() } {
        *set &= !(1 << (signo as usize - 1));
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn sigemptyset(set: *mut sigset_t) -> c_int {
    if let Some(set) = (set as *mut SigSet).as_mut() {
        *set = 0;
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn sigfillset(set: *mut sigset_t) -> c_int {
    if let Some(set) = (set as *mut SigSet).as_mut() {
        *set = (1 << NSIG) - 1;
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn sigismember(set: *const sigset_t, signo: c_int) -> c_int {
    if signo <= 0 || signo as usize > NSIG {
        ERRNO.set(libc::EINVAL);
        return -1;
    }

    if let Some(set) = unsafe { (set as *mut SigSet).as_mut() } {
        if *set & (1 << (signo as usize - 1)) != 0 {
            return 1;
        }
    }
    0
}

#[no_mangle]
pub extern "C" fn signal(
    sig: c_int,
    func: Option<extern "C" fn(c_int)>,
) -> Option<extern "C" fn(c_int)> {
    let sa = sigaction {
        sa_handler: func,
        sa_restorer: None,
        sa_flags: SA_RESTART as _,
        sa_mask: sigset_t::default(),
    };
    let mut old_sa = mem::MaybeUninit::uninit();
    if unsafe { sigaction(sig, &sa, old_sa.as_mut_ptr()) } < 0 {
        return unsafe { mem::transmute::<isize, Option<extern "C" fn(i32)>>(SIG_ERR) };
    }
    unsafe { old_sa.assume_init() }.sa_handler
}

#[no_mangle]
pub unsafe extern "C" fn sigpending(set: *mut sigset_t) -> c_int {
    bk_syscall!(RtSigPending, set) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigprocmask(
    how: c_int,
    set: *const sigset_t,
    oset: *mut sigset_t,
) -> c_int {
    // only process posix standard signals
    bk_syscall!(RtSigProcmask, how, set, oset) as c_int
}

#[no_mangle]
pub extern "C" fn sigqueue(pid: pid_t, sig: c_int, val: sigval) -> c_int {
    bk_syscall!(RtSigQueueInfo, pid, sig, val.sival_ptr) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigsuspend(sigmask: *const sigset_t) -> c_int {
    bk_syscall!(RtSigSuspend, sigmask) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigtimedwait(
    set: *const sigset_t,
    sig: *mut siginfo_t,
    tp: *const timespec,
) -> c_int {
    bk_syscall!(RtSigTimedWait, set, sig as *mut c_void, tp) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn sigwait(set: *const sigset_t, sig: *mut c_int) -> c_int {
    let mut pinfo = mem::MaybeUninit::<siginfo_t>::uninit();
    if sigtimedwait(set, pinfo.as_mut_ptr(), ptr::null_mut()) < 0 {
        return -1;
    }
    let info = pinfo.assume_init();
    (*sig) = info.si_signo;
    0
}

#[no_mangle]
pub unsafe extern "C" fn sigwaitinfo(set: *const sigset_t, sig: *mut siginfo_t) -> c_int {
    sigtimedwait(set, sig, core::ptr::null())
}
