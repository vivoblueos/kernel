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

extern crate alloc;
use core::ffi::{c_size_t, c_ssize_t};

use crate::{
    arch, asynk, net, scheduler,
    sync::atomic_wait as futex,
    thread::{self, Builder, Entry, Stack, Thread, ThreadNode},
    time,
    vfs::syscalls as vfs_syscalls,
};
use alloc::boxed::Box;
use blueos_header::{
    syscalls::NR,
    thread::{ExitArgs, SpawnArgs},
};
use core::sync::atomic::AtomicUsize;
use libc::{
    addrinfo, c_char, c_int, c_ulong, c_void, clockid_t, mode_t, msghdr, off_t, sigset_t, size_t,
    sockaddr, socklen_t, timespec, EINVAL,
};

#[repr(C)]
#[derive(Default)]
pub struct Context {
    pub nr: usize,
    pub args: [usize; 6],
}

pub use crate::vfs::syscalls::{Stat, Statfs as StatFs};
/// this signal data structure will be used in signal handling
/// now add attributes to disable warnings
/// copy from librs/signal/mod.rs
#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone)]
pub struct sigaltstack {
    pub ss_sp: *mut c_void,
    pub ss_flags: c_int,
    pub ss_size: size_t,
}

/// copy from librs/signal/mod.rs
#[allow(non_camel_case_types)]
#[repr(align(8))]
pub struct siginfo_t {
    pub si_signo: c_int,
    pub si_errno: c_int,
    pub si_code: c_int,
    _pad: [c_int; 29],
    _align: [usize; 0],
}

/// copy from librs/signal/mod.rs
#[allow(non_camel_case_types)]
pub struct sigaction {
    pub sa_handler: Option<extern "C" fn(c_int)>,
    pub sa_flags: c_ulong,
    pub sa_restorer: Option<unsafe extern "C" fn()>,
    pub sa_mask: sigset_t,
}

// For every syscall number in NR, we have to define a module to
// handle the syscall request.  `handle_context` serves as the
// dispatcher if syscall is invoked via software interrupt.
// bk_syscall! macro should be used by external libraries if syscall
// is invoked via function call.
macro_rules! syscall_table {
    ($(($nr:tt, $mod:ident),)*) => {
        pub(crate) fn dispatch_syscall(ctx: &Context) -> usize {
            match ctx.nr {
                $(val if val == NR::$nr as usize =>
                    return $crate::syscalls::$mod::handle_context(ctx) as usize,)*
                _ => return usize::MAX,
            }
        }

        #[macro_export]
        macro_rules! bk_syscall {
            $(($nr $$(,$arg:expr)*) => { $crate::syscalls::$mod::handle($$($arg),*) });*
        }
    };
}

macro_rules! map_args {
    ($args:expr, $idx:expr) => {};
    ($args:expr, $idx:expr, $arg:ident, $argty:ty $(, $tailarg:ident, $tailargty:ty)*) => {
        let $arg = unsafe { core::mem::transmute_copy::<usize, $argty>(&$args[$idx]) };
        map_args!($args, $idx+1 $(, $tailarg, $tailargty)*);
    };
}

// A helper macro to implement syscall handler quickly.
macro_rules! define_syscall_handler {
    ($handler:ident($($arg:ident: $argty:ty),*)
                    -> $ret:ty $body:block
    ) => (
        pub mod $handler {
            use super::*;
            use core::ffi::c_long;

            // FIXME: Rustc miscompiles if inlined.
            #[inline(never)]
            pub fn handle($($arg: $argty),*) -> $ret {
                $body
            }

            pub fn handle_context(ctx: &Context) -> usize {
                map_args!(ctx.args, 0 $(, $arg, $argty)*);
                handle($($arg),*) as usize
            }
        }
    )
}

define_syscall_handler!(
nop() -> c_long {
    0
});

define_syscall_handler!(
get_tid() -> c_long {
    let t = scheduler::current_thread();
    let handle = Thread::id(&t);
    handle as c_long
});

define_syscall_handler!(
create_thread(spawn_args_ptr: *const SpawnArgs) -> c_long {
    let spawn_args = unsafe {&*spawn_args_ptr};
    let t = thread::Builder::new(Entry::Posix(spawn_args.entry, spawn_args.arg))
        .set_stack(Stack::from_raw(
            spawn_args.stack_start as *mut u8,
            spawn_args.stack_size))
        .build();
    let handle = Thread::id(&t);
    if let Some(f) = spawn_args.spawn_hook { f(handle, spawn_args); }
    let ok = scheduler::queue_ready_thread(thread::CREATED, t);
    // We don't increment the rc of the created thread since it's also
    // referenced by the global queue. When this thread is retired,
    // it's removed from the global queue.
    assert!(ok);
    unsafe {core::mem::transmute(handle)}
});

define_syscall_handler!(
atomic_wait(addr: usize, val: usize, timeout: *const timespec) -> c_long {
    let timeout = if timeout.is_null() {
        None
    } else {
        let timeout = unsafe { &*timeout };
        Some(time::tick_from_millisecond((timeout.tv_sec * 1000 + timeout.tv_nsec / 1000000) as usize))
    };
    let ptr = addr as *const AtomicUsize;
    let atom = unsafe { &*ptr };
    futex::atomic_wait(atom, val, timeout).map_or_else(|e|e.to_errno() as c_long, |_| 0)
});

define_syscall_handler!(
atomic_wake(addr: usize, count: *mut usize) -> c_long {
    let how_many = unsafe { *count };
    let ptr = addr as *const AtomicUsize;
    let atom = unsafe { &*ptr };
    futex::atomic_wake(atom, how_many).map_or_else(|_| -1, |woken| {
        unsafe { *count = woken };
        0
    })
});

// Only for posix testsuite, we need to implement a stub for clock_gettime
define_syscall_handler!(
    clock_gettime(_clk_id: clockid_t, tp: *mut timespec) -> c_long {
        0
});

define_syscall_handler!(
alloc_mem(ptr: *mut *mut c_void, size: usize, align: usize) -> c_long {
    let addr = crate::allocator::malloc_align(size, align);
    if addr.is_null() {
        return -1;
    }
    unsafe { ptr.write(addr as *mut c_void) };
    0
});

define_syscall_handler!(
free_mem(ptr: *mut c_void) -> c_long {
    crate::allocator::free(ptr as *mut u8);
    0
});

define_syscall_handler!(
write(fd: i32, buf: *const u8, size: usize) -> c_long {
    unsafe {
        vfs_syscalls::write(
        fd,
        buf, size) as c_long
    }
});

define_syscall_handler!(open(path: *const c_char, flags: c_int, mode: mode_t) -> c_int {
    vfs_syscalls::open(path, flags, mode)
});

define_syscall_handler!(
    close(fd: c_int) -> c_int {
        vfs_syscalls::close(fd)
    }
);
define_syscall_handler!(
    read(fd: c_int, buf: *mut c_void, count: size_t) -> isize {
        vfs_syscalls::read(fd, buf as *mut u8, count as usize)
    }
);

define_syscall_handler!(
    lseek(fildes: c_int, offset: usize, whence: c_int) -> c_int {
        vfs_syscalls::lseek(fildes, offset as i64, whence) as c_int
    }
);

async fn cleanup_for_exited_thread(exit_args: ExitArgs) {
    let Some(ref hook) = exit_args.exit_hook else {
        return;
    };
    hook(&exit_args);
}

define_syscall_handler!(exit_thread(exit_args: *const ExitArgs) -> c_long {
    if exit_args.is_null() {
        scheduler::retire_me();
        return -1;
    }
    let t = scheduler::current_thread();
    let id = Thread::id(&t);
    let exit_args = unsafe{ &*exit_args };
    // We can't assume there is no syscalls inside the exit hook, so that we
    // can't run the exit hook in the cleanup stage which happens during context
    // switch. We resort to asynk.
    if let Some(ref hook) = exit_args.exit_hook {
        let hook = move || {
            let fut = cleanup_for_exited_thread(exit_args.clone());
            asynk::spawn(fut);
        };
        t.lock().set_cleanup(Entry::Closure(Box::new(hook)));
    }
    scheduler::retire_me();
    -1
});

define_syscall_handler!(sched_yield() -> c_long {
    scheduler::yield_me();
    0
});
define_syscall_handler!(
    rmdir(path: *const c_char) -> c_int {
        vfs_syscalls::rmdir(path)
    }
);
define_syscall_handler!(
    link(oldpath: *const c_char, newpath: *const c_char) -> c_int {
        vfs_syscalls::link(oldpath, newpath)
    }
);
define_syscall_handler!(
    unlink(path: *const c_char) -> c_int {
        vfs_syscalls::unlink(path)
    }
);
define_syscall_handler!(
    fcntl(fildes: c_int, cmd: c_int, arg: usize) -> c_int {
        vfs_syscalls::fcntl(fildes, cmd, arg)
    }
);
define_syscall_handler!(
    stat(path: *const c_char, buf: *mut c_char) -> c_int {
        vfs_syscalls::stat(path, buf as *mut Stat) as c_int
    }
);

define_syscall_handler!(
    fstat(fd: c_int, buf: *mut c_char) -> c_int {
        vfs_syscalls::fstat(fd, buf as *mut Stat) as c_int
    }
);
define_syscall_handler!(
    mkdir(path: *const c_char, mode: mode_t) -> c_int {
        vfs_syscalls::mkdir(path, mode)
    }
);
define_syscall_handler!(
    statfs(path: *const c_char, buf: *mut c_char) -> c_int {
        vfs_syscalls::statfs(path, buf as *mut StatFs) as c_int
    }
);

define_syscall_handler!(
    fstatfs(fd: c_int, buf: *mut c_char) -> c_int {
        vfs_syscalls::fstatfs(fd, buf as *mut StatFs) as c_int
    }
);

define_syscall_handler!(
    getdents(fd: c_int, buf: *mut c_void, size: usize) -> isize {
        vfs_syscalls::getdents(fd, buf as *mut u8, size as usize) as isize
    }
);
define_syscall_handler!(
    chdir(path: *const c_char) -> c_int {
        vfs_syscalls::chdir(path)
    }
);
define_syscall_handler!(
    getcwd(buf: *mut c_char, size: size_t) -> c_int {
        vfs_syscalls::getcwd(buf, size as usize) as c_int
    }
);
define_syscall_handler!(
    ftruncate(fd: c_int, length: off_t) -> c_int {
        vfs_syscalls::ftruncate(fd, length)
    }
);
define_syscall_handler!(
    mount(
        source: *const c_char,
        target: *const c_char,
        fstype: *const c_char,
        flags: c_ulong,
        data: *const c_void
    ) -> c_int {
        vfs_syscalls::mount(
            source,
            target,
            fstype,
            flags as core::ffi::c_ulong,
            data as *const core::ffi::c_void
        )
    }
);
define_syscall_handler!(
    umount(target: *const c_char) -> c_int {
        vfs_syscalls::umount(target)
    }
);
define_syscall_handler!(
    signalaction(_signum: c_int, _act: *const c_void, _oact: *mut c_void) -> c_int {
        // TODO: implement signalaction
        0
    }
);
define_syscall_handler!(
    signaltstack(_ss: *const c_void, _old_ss: *mut c_void) -> c_int {
        0
    }
);
define_syscall_handler!(
    sigpending(_set: *mut libc::sigset_t) -> c_int {
        0
    }
);
define_syscall_handler!(
    sigprocmask(_how: c_int, _set: *const libc::sigset_t, _oldset: *mut libc::sigset_t) -> c_int {
        0
    }
);
define_syscall_handler!(
    sigqueueinfo(_pid: c_int, _sig: c_int, _info: *const c_void) -> c_int {
        0
    }
);
define_syscall_handler!(
    sigsuspend(_set: *const libc::sigset_t) -> c_int {
        0
    }
);
define_syscall_handler!(
    sigtimedwait(_set: *const sigset_t, _info: *mut c_void, _timeout: *const timespec) -> c_int {
        0
    }
);

// Socket syscall begin
define_syscall_handler!(
    socket(domain: c_int, type_: c_int, protocol_: c_int) -> c_int {
        unsafe{
            net::syscalls::socket(domain, type_, protocol_)
        }
    }
);

define_syscall_handler!(
    bind(sockfd: c_int, addr: *const sockaddr, len: socklen_t) -> c_int {
        net::syscalls::bind(sockfd, addr, len)
    }
);

define_syscall_handler!(
    connect(sockfd: c_int, addr: *const sockaddr, len: socklen_t) -> c_int {
        net::syscalls::connect(sockfd, addr, len)
    }
);

define_syscall_handler!(
    listen(sockfd: c_int, backlog: c_int) -> c_int {
        unsafe {
            net::syscalls::listen(sockfd, backlog)
        }
    }
);

define_syscall_handler!(
    accept(sockfd: c_int, addr: *mut sockaddr, len: *mut socklen_t) -> c_int {
        let orig_len = if !len.is_null() { unsafe { *len } } else { 0 };

        let result = net::syscalls::accept(
            sockfd,
            addr as *const sockaddr,
            orig_len
        );
        if !len.is_null() && result >= 0 {
            unsafe { *len = orig_len };
        }

        result
    }
);

define_syscall_handler!(
    send(sockfd: c_int, buffer: *const core::ffi::c_void, length: c_size_t, flags: c_int) -> c_ssize_t {
        net::syscalls::send(sockfd, buffer, length, flags)
    }
);

define_syscall_handler!(
    sendto(sockfd: c_int, message: *const core::ffi::c_void, length: c_size_t, flags: c_int, dest_addr: *const sockaddr, dest_len: socklen_t) -> c_ssize_t {
        net::syscalls::sendto(sockfd, message, length, flags, dest_addr, dest_len)
    }
);

define_syscall_handler!(
    recv(sockfd: c_int, buffer: *mut core::ffi::c_void, length: c_size_t, flags: c_int) -> c_ssize_t {
        net::syscalls::recv(sockfd, buffer, length, flags)
    }
);

define_syscall_handler!(
    recvfrom(sockfd: c_int, buffer: *mut core::ffi::c_void, length: c_size_t, flags: c_int, address: *mut sockaddr, address_len: *mut socklen_t) -> c_ssize_t {
        net::syscalls::recvfrom(sockfd, buffer, length, flags, address, address_len)
    }
);

define_syscall_handler!(
    shutdown(sockfd: c_int, how: c_int) -> c_int {
        unsafe {
            net::syscalls::shutdown(sockfd, how)
        }
    }
);

define_syscall_handler!(
    setsockopt(sockfd: c_int, level: c_int, option_name: c_int, option_value: *const core::ffi::c_void, option_len: socklen_t) -> c_int {
        net::syscalls::setsockopt(sockfd, level, option_name, option_value, option_len)
    }
);

define_syscall_handler!(
    getsockopt(sockfd: c_int, level: c_int, option_name: c_int, option_value: *mut core::ffi::c_void, option_len: *mut socklen_t) -> c_int {
        net::syscalls::getsockopt(sockfd, level, option_name, option_value, option_len)
    }
);

define_syscall_handler!(
    sendmsg(sockfd: c_int, message: *const msghdr, flags: c_int) -> c_ssize_t {
        net::syscalls::sendmsg(sockfd, message, flags)
    }
);

define_syscall_handler!(
    recvmsg(sockfd: c_int, message: *mut msghdr, flags: c_int) -> c_ssize_t {
        net::syscalls::recvmsg(sockfd, message, flags)
    }
);
// Socket syscall end

// Netdb syscall begin
define_syscall_handler!(
    getaddrinfo(node: *const c_char,
        service: *const c_char,
        hints: *const addrinfo,
        res: *mut *mut addrinfo) -> c_int {
        net::syscalls::getaddrinfo(node, service, hints, res)
    }
);
define_syscall_handler!(
    freeaddrinfo(res: *mut addrinfo) -> usize {
        net::syscalls::freeaddrinfo(res)
    }
);
// Netdb syscall end

define_syscall_handler!(
    sys_clock_nanosleep(
        clock_id: i32,
        flags: i32,
        rqtp: *const timespec,
        rmtp: *mut timespec
    ) -> c_int {
        // TODO: Valid Clock Id

        // TODO: Valid rqtp

        // TODO: Implement absolute time sleep
        let duration = timespec {
            tv_sec: unsafe { rqtp.read().tv_sec },
            tv_nsec: unsafe { rqtp.read().tv_nsec },
        };

        // TODO: Implement tv_nsec
        let ticks = blueos_kconfig::TICKS_PER_SECOND * duration.tv_sec as usize;
        scheduler::suspend_me_for(ticks);
        0
    }
);

syscall_table! {
    (Echo, echo),
    (Nop, nop),
    (GetTid, get_tid),
    (CreateThread, create_thread),
    (ExitThread, exit_thread),
    (AtomicWake, atomic_wake),
    (AtomicWait, atomic_wait),
    // For test only
    (ClockGetTime, clock_gettime),
    (AllocMem, alloc_mem),
    (FreeMem, free_mem),
    (Write, write),
    (Close, close),
    (Read, read),
    (Open, open),
    (Lseek, lseek),
    (SchedYield, sched_yield),
    (Rmdir, rmdir),
    (Link, link),
    (Unlink, unlink),
    (Fcntl, fcntl),
    (Stat, stat),
    (FStat, fstat),
    (Statfs, statfs),
    (FStatfs, fstatfs),
    (Mkdir, mkdir),
    (GetDents, getdents),
    (Chdir, chdir),
    (Getcwd, getcwd),
    (Ftruncate, ftruncate),
    (Mount, mount),
    (Umount, umount),
    (RtSigAction, signalaction),
    (SigAltStack, signaltstack),
    (RtSigPending, sigpending),
    (RtSigProcmask, sigprocmask),
    (RtSigQueueInfo, sigqueueinfo),
    (RtSigSuspend, sigsuspend),
    (RtSigTimedWait, sigtimedwait),
    (Socket, socket),
    (Bind, bind),
    (Connect, connect),
    (Listen,listen),
    (Accept,accept),
    (Send,send),
    (Sendto,sendto),
    (Recv,recv),
    (Recvfrom,recvfrom),
    (Shutdown,shutdown),
    (Setsockopt,setsockopt),
    (Getsockopt,getsockopt),
    (Sendmsg,sendmsg),
    (Recvmsg,recvmsg),
    (GetAddrinfo,getaddrinfo),
    (FreeAddrinfo,freeaddrinfo),
    (NanoSleep,sys_clock_nanosleep),
}

// Begin syscall modules.
pub mod echo;
// End syscall modules.
