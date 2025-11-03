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

#[cfg(kernel_async)]
use crate::asynk;
#[cfg(enable_net)]
use crate::net::syscalls as net_syscalls;
#[cfg(enable_vfs)]
use crate::vfs::syscalls as vfs_syscalls;
#[cfg(enable_vfs)]
pub use crate::vfs::syscalls::{Stat, Statfs as StatFs};
use crate::{
    scheduler,
    sync::atomic_wait as futex,
    thread::{self, Builder, Entry, Stack, Thread},
    time,
};

pub use crate::sync::posix_mqueue;
use alloc::boxed::Box;
use blueos_header::{syscalls::NR, thread::SpawnArgs};
use core::{
    ffi::{c_size_t, c_ssize_t},
    sync::atomic::AtomicUsize,
};
use libc::{
    addrinfo, c_char, c_int, c_long, c_uint, c_ulong, c_void, clockid_t, mode_t, msghdr, off_t,
    sigset_t, size_t, sockaddr, socklen_t, timespec, EINVAL,
};

#[cfg(not(enable_vfs))]
mod vfs_syscalls {
    use super::*;
    pub struct Stat;
    pub struct StatFs;
    pub fn write(_fd: i32, _buf: *const u8, _size: usize) -> isize {
        -libc::ENOTSUP as isize
    }
    pub fn read(_fd: i32, _buf: *mut u8, _size: usize) -> isize {
        -libc::ENOTSUP as isize
    }
    pub fn lseek(_fd: i32, _offset: i64, _whence: i32) -> i64 {
        -libc::ENOTSUP as i64
    }
    pub fn close(_fd: i32) -> i32 {
        -libc::ENOTSUP
    }
    pub fn open(_path: *const c_char, _flags: c_int, _mode: mode_t) -> i32 {
        -libc::ENOTSUP
    }
    pub fn rmdir(_path: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn link(_oldpath: *const c_char, _newpath: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn unlink(_path: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn fcntl(_fildes: c_int, _cmd: c_int, _arg: usize) -> i32 {
        -libc::ENOTSUP
    }
    pub fn stat(_path: *const c_char, _buf: *mut Stat) -> i32 {
        -libc::ENOTSUP
    }
    pub fn fstat(_fd: c_int, _buf: *mut Stat) -> i32 {
        -libc::ENOTSUP
    }
    pub fn mkdir(_path: *const c_char, _mode: mode_t) -> i32 {
        -libc::ENOTSUP
    }
    pub fn statfs(_path: *const c_char, _buf: *mut StatFs) -> i32 {
        -libc::ENOTSUP
    }
    pub fn fstatfs(_fd: c_int, _buf: *mut StatFs) -> i32 {
        -libc::ENOTSUP
    }
    pub fn getdents(_fd: c_int, _buf: *mut u8, _size: usize) -> isize {
        -libc::ENOTSUP as isize
    }
    pub fn chdir(_path: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn getcwd(_buf: *mut c_char, _size: size_t) -> i32 {
        -libc::ENOTSUP
    }
    pub fn ftruncate(_fd: c_int, _length: off_t) -> i32 {
        -libc::ENOTSUP
    }
    pub fn mount(
        _source: *const c_char,
        _target: *const c_char,
        _fstype: *const c_char,
        _flags: core::ffi::c_ulong,
        _data: *const core::ffi::c_void,
    ) -> i32 {
        -libc::ENOTSUP
    }
    pub fn umount(_target: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
}
#[cfg(not(enable_vfs))]
use vfs_syscalls::{Stat, StatFs};

#[cfg(not(enable_net))]
mod net_syscalls {
    use super::*;
    pub fn socket(_domain: c_int, _type: c_int, _protocol: c_int) -> c_int {
        -libc::ENOTSUP
    }
    pub fn bind(_socket: c_int, _address: *const sockaddr, _address_len: socklen_t) -> c_int {
        -libc::ENOTSUP
    }
    pub fn connect(_socket: c_int, _address: *const sockaddr, _address_len: socklen_t) -> c_int {
        -libc::ENOTSUP
    }
    pub fn listen(_socket: c_int, _backlog: c_int) -> c_int {
        -libc::ENOTSUP
    }
    pub fn accept(_socket: c_int, _address: *const sockaddr, _address_len: u32) -> c_int {
        -libc::ENOTSUP
    }
    pub fn send(
        _socket: c_int,
        _buffer: *const core::ffi::c_void,
        _length: c_size_t,
        _flags: c_int,
    ) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn sendto(
        _socket: c_int,
        _buffer: *const core::ffi::c_void,
        _length: c_size_t,
        _flags: c_int,
        _dest_addr: *const sockaddr,
        _dest_len: socklen_t,
    ) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn recv(
        _socket: c_int,
        _buffer: *mut core::ffi::c_void,
        _length: c_size_t,
        _flags: c_int,
    ) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn recvfrom(
        _socket: c_int,
        _buffer: *mut core::ffi::c_void,
        _length: c_size_t,
        _flags: c_int,
        _address: *mut sockaddr,
        _address_len: *mut socklen_t,
    ) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn shutdown(_socket: c_int, _how: c_int) -> c_int {
        -libc::ENOTSUP
    }
    pub fn setsockopt(
        _socket: c_int,
        _level: c_int,
        _option_name: c_int,
        _option_value: *const core::ffi::c_void,
        _option_len: socklen_t,
    ) -> c_int {
        -libc::ENOTSUP
    }
    pub fn getsockopt(
        _socket: c_int,
        _level: c_int,
        _option_name: c_int,
        _option_value: *mut core::ffi::c_void,
        _option_len: *mut socklen_t,
    ) -> c_int {
        -libc::ENOTSUP
    }
    pub fn sendmsg(_socket: c_int, _message: *const msghdr, _flags: c_int) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn recvmsg(_socket: c_int, _message: *mut msghdr, _flags: c_int) -> c_ssize_t {
        -libc::ENOTSUP as c_ssize_t
    }
    pub fn getaddrinfo(
        _node: *const c_char,
        _service: *const c_char,
        _hints: *const addrinfo,
        _res: *mut *mut addrinfo,
    ) -> c_int {
        -libc::ENOTSUP
    }
    pub fn freeaddrinfo(_res: *mut addrinfo) -> usize {
        0
    }
}

#[repr(C)]
#[derive(Default)]
pub struct Context {
    pub nr: usize,
    pub args: [usize; 6],
}

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

#[repr(C)]
pub struct mq_attr {
    pub mq_flags: c_long,
    pub mq_maxmsg: c_long,
    pub mq_msgsize: c_long,
    pub mq_curmsgs: c_long,
    pub pad: [c_long; 4],
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
        .set_stack(Stack::from_raw(spawn_args.stack_start, spawn_args.stack_size))
        .build();
    if let Some(cleanup) = spawn_args.cleanup {
        t.lock().set_cleanup(Entry::Posix(cleanup, spawn_args.arg));
    };
    let handle = Thread::id(&t);
    if let Some(f) = spawn_args.spawn_hook { f(handle, spawn_args_ptr); }
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
        // only support CLOCK_MONOTONIC
        const TICK_TO_NANOSECOND: usize = 1_000_000_000 / blueos_kconfig::TICKS_PER_SECOND;
        let ticks = time::get_sys_ticks();
        let seconds = ticks / blueos_kconfig::TICKS_PER_SECOND;
        let nanoseconds = (ticks % blueos_kconfig::TICKS_PER_SECOND) * TICK_TO_NANOSECOND;
        unsafe {
            *tp = timespec { tv_sec: seconds as c_int, tv_nsec: nanoseconds as c_int };
        }
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

define_syscall_handler!(exit_thread() -> c_long {
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
            net_syscalls::socket(domain, type_, protocol_)
        }
    }
);

define_syscall_handler!(
    bind(sockfd: c_int, addr: *const sockaddr, len: socklen_t) -> c_int {
        net_syscalls::bind(sockfd, addr, len)
    }
);

define_syscall_handler!(
    connect(sockfd: c_int, addr: *const sockaddr, len: socklen_t) -> c_int {
        net_syscalls::connect(sockfd, addr, len)
    }
);

define_syscall_handler!(
    listen(sockfd: c_int, backlog: c_int) -> c_int {
        unsafe {
            net_syscalls::listen(sockfd, backlog)
        }
    }
);

define_syscall_handler!(
    accept(sockfd: c_int, addr: *mut sockaddr, len: *mut socklen_t) -> c_int {
        let orig_len = if !len.is_null() { unsafe { *len } } else { 0 };

        let result = net_syscalls::accept(
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
        net_syscalls::send(sockfd, buffer, length, flags)
    }
);

define_syscall_handler!(
    sendto(sockfd: c_int, message: *const core::ffi::c_void, length: c_size_t, flags: c_int, dest_addr: *const sockaddr, dest_len: socklen_t) -> c_ssize_t {
        net_syscalls::sendto(sockfd, message, length, flags, dest_addr, dest_len)
    }
);

define_syscall_handler!(
    recv(sockfd: c_int, buffer: *mut core::ffi::c_void, length: c_size_t, flags: c_int) -> c_ssize_t {
        net_syscalls::recv(sockfd, buffer, length, flags)
    }
);

define_syscall_handler!(
    recvfrom(sockfd: c_int, buffer: *mut core::ffi::c_void, length: c_size_t, flags: c_int, address: *mut sockaddr, address_len: *mut socklen_t) -> c_ssize_t {
        net_syscalls::recvfrom(sockfd, buffer, length, flags, address, address_len)
    }
);

define_syscall_handler!(
    shutdown(sockfd: c_int, how: c_int) -> c_int {
        unsafe {
            net_syscalls::shutdown(sockfd, how)
        }
    }
);

define_syscall_handler!(
    setsockopt(sockfd: c_int, level: c_int, option_name: c_int, option_value: *const core::ffi::c_void, option_len: socklen_t) -> c_int {
        net_syscalls::setsockopt(sockfd, level, option_name, option_value, option_len)
    }
);

define_syscall_handler!(
    getsockopt(sockfd: c_int, level: c_int, option_name: c_int, option_value: *mut core::ffi::c_void, option_len: *mut socklen_t) -> c_int {
        net_syscalls::getsockopt(sockfd, level, option_name, option_value, option_len)
    }
);

define_syscall_handler!(
    sendmsg(sockfd: c_int, message: *const msghdr, flags: c_int) -> c_ssize_t {
        net_syscalls::sendmsg(sockfd, message, flags)
    }
);

define_syscall_handler!(
    recvmsg(sockfd: c_int, message: *mut msghdr, flags: c_int) -> c_ssize_t {
        net_syscalls::recvmsg(sockfd, message, flags)
    }
);
// Socket syscall end

// Netdb syscall begin
define_syscall_handler!(
    getaddrinfo(node: *const c_char,
        service: *const c_char,
        hints: *const addrinfo,
        res: *mut *mut addrinfo) -> c_int {
        net_syscalls::getaddrinfo(node, service, hints, res)
    }
);
define_syscall_handler!(
    freeaddrinfo(res: *mut addrinfo) -> usize {
        net_syscalls::freeaddrinfo(res);
        0
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
        let ticks = blueos_kconfig::TICKS_PER_SECOND * duration.tv_sec as usize +
                    duration.tv_nsec as usize / (1000000000 / blueos_kconfig::TICKS_PER_SECOND);
        if ticks == 0 {
            scheduler::yield_me();
        } else {
            scheduler::suspend_me_for(ticks);
        }
        0
    }
);

define_syscall_handler!(
    mq_open(name: *const c_char, oflag: c_int, mode: mode_t, attr: *const c_void) -> c_int {
        posix_mqueue::mq_open(name, oflag, mode, attr as *const mq_attr)
    }
);

define_syscall_handler!(
    mq_close(mqdes: c_int) -> c_int {
        posix_mqueue::mq_close(mqdes)
    }
);
define_syscall_handler!(
    mq_unlink(name: *const c_char) -> c_int {
        posix_mqueue::mq_unlink(name)
    }
);
define_syscall_handler!(
    mq_send(mqdes: c_int, msg_ptr: *const c_char, msg_len: size_t, msg_prio: c_uint) -> c_int {
        posix_mqueue::mq_timedsend(mqdes, msg_ptr, msg_len, msg_prio, core::ptr::null())
    }
);
define_syscall_handler!(
    mq_timedsend(mqdes: c_int, msg_ptr: *const c_char, msg_len: size_t, msg_prio: c_uint, timeout: *const timespec) -> c_int {
        posix_mqueue::mq_timedsend(mqdes, msg_ptr, msg_len, msg_prio, timeout)
    }
);
define_syscall_handler!(
    mq_receive(mqdes: c_int, msg_ptr: *mut c_char, msg_len: size_t, msg_prio: *mut c_uint) -> c_int {
        posix_mqueue::mq_timedrecv(mqdes, msg_ptr, msg_len, msg_prio, core::ptr::null())
    }
);
define_syscall_handler!(
    mq_timedreceive(mqdes: c_int, msg_ptr: *mut c_char, msg_len: size_t, msg_prio: *mut c_uint, timeout: *const timespec) -> c_int {
        posix_mqueue::mq_timedrecv(mqdes, msg_ptr, msg_len, msg_prio, timeout)
    }
);
define_syscall_handler!(
    mq_getsetattr(mqdes: c_int, new: *const c_void, old: *mut c_void) -> c_int {
        posix_mqueue::mq_getsetattr(mqdes, new as *const mq_attr, old as *mut mq_attr)
    }
);

#[cfg(enable_syscall)]
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
    (MqOpen, mq_open),
    (MqClose, mq_close),
    (MqUnlink, mq_unlink),
    (MqTimedSend, mq_timedsend),
    (MqTimedReceive, mq_timedreceive),
    (MqGetSetAttr, mq_getsetattr),
}

#[cfg(not(enable_syscall))]
pub fn dispatch_syscall(ctx: &Context) -> usize {
    0
}

// Begin syscall modules.
pub mod echo;
// End syscall modules.
