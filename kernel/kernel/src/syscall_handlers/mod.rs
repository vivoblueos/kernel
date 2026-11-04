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
    config, scheduler,
    sync::atomic_wait as futex,
    thread::{self, Builder, Entry, Stack, Thread},
    time,
    time::Tick,
};

pub use crate::sync::posix_mqueue;
use alloc::boxed::Box;
use blueos_header::{syscalls::NR, thread::SpawnArgs};
use core::{
    ffi::{c_size_t, c_ssize_t},
    sync::atomic::AtomicUsize,
};
use libc::{
    addrinfo, c_char, c_int, c_long, c_uint, c_ulong, c_void, clockid_t, itimerspec, mode_t,
    msghdr, off_t, sigevent, sigset_t, size_t, sockaddr, socklen_t, time_t, timer_t, timespec,
    EBUSY, EINVAL, ESRCH,
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
    pub fn pipe(_fds: *mut c_int, _flags: c_int) -> c_int {
        -libc::ENOTSUP
    }
    pub fn dup2(_oldfd: c_int, _newfd: c_int) -> c_int {
        -libc::ENOTSUP
    }
    pub fn rmdir(_path: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn link(_oldpath: *const c_char, _newpath: *const c_char) -> i32 {
        -libc::ENOTSUP
    }
    pub fn rename(_oldpath: *const c_char, _newpath: *const c_char) -> i32 {
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
    pub fn ioctl(_fd: c_int, _request: c_ulong, _arg: *mut core::ffi::c_void) -> c_int {
        -libc::ENOTSUP
    }
    pub fn poll(
        _fds: *mut core::ffi::c_void,
        _nfds: usize,
        _timeout_ms: c_int,
    ) -> core::ffi::c_long {
        -libc::ENOTSUP as core::ffi::c_long
    }
    pub fn ppoll(
        _fds: *mut core::ffi::c_void,
        _nfds: usize,
        _timeout: *const timespec,
        _sigmask: *const sigset_t,
    ) -> core::ffi::c_long {
        -libc::ENOTSUP as core::ffi::c_long
    }
    pub fn select(
        _nfds: c_int,
        _readfds: *mut core::ffi::c_void,
        _writefds: *mut core::ffi::c_void,
        _exceptfds: *mut core::ffi::c_void,
        _timeout: *mut libc::timeval,
    ) -> c_int {
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
    pub fn accept(_socket: c_int, _address: *mut sockaddr, _address_len: *mut socklen_t) -> c_int {
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
    /// Opaque pointer to the architecture's saved trap frame, or null.
    ///
    /// Almost no syscall needs it: arguments are in registers, and a result is
    /// returned in `a0`. `fork` is the exception — it has to copy the parent's
    /// *entire* register state so the child resumes exactly where the parent
    /// left off, and that state exists only in the frame the trap entry built.
    /// Passing the address through here keeps the dispatcher free of any
    /// architecture-specific type.
    ///
    /// Only valid for the duration of the dispatch: it points at the caller's
    /// own stack frame.
    pub frame: usize,
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
macro_rules! syscall_table {
    ($(($nr:tt, $mod:ident),)*) => {
        pub(crate) fn dispatch_syscall(ctx: &Context) -> usize {
            match ctx.nr {
                $(val if val == NR::$nr as usize =>
                    return $crate::syscalls::$mod::handle_context(ctx) as usize,)*
                _ => return usize::MAX,
            }
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
get_sched_param(tid: usize) -> c_long {

    let target = thread::GlobalQueueVisitor::find_if(|t| {
        thread::Thread::id(t) == tid
    });
    let Some(target) = target else {
        return -(ESRCH as c_long);
    };
    target.priority() as c_long
});

define_syscall_handler!(
set_sched_param(tid: usize, prio: c_int) -> c_long {
    if prio < 0 || (prio as u32) > (config::MAX_THREAD_PRIORITY as u32) {
        return -(EINVAL as c_long);
    }
    let p = prio as crate::types::ThreadPriority;
    let mut was_ready = false;
    let target = thread::GlobalQueueVisitor::find_if(|t| {
        if thread::Thread::id(t) == tid {
            was_ready = t.state() == thread::READY;
            if !was_ready {
                let mut w = t.lock();
                w.set_origin_priority(p);
                w.set_priority(p);
            }
            true
        } else {
            false
        }
    });

    let Some(target) = target else {
        return -(ESRCH as c_long);
    };

    let preempt_guard = thread::Thread::try_preempt_me();
    let ret = if was_ready {
        match scheduler::update_ready_thread_priority(&target, p) {
            Ok(()) => 0,
            Err(_) => -(EBUSY as c_long),
        }
    } else {
        0
    };
    drop(preempt_guard);
    ret
});

define_syscall_handler!(
create_thread(spawn_args_ptr: *const SpawnArgs) -> c_long {
    // A U-mode caller gets a thread that starts in U-mode, in the caller's own
    // address space. That is a different construction from the kernel-thread
    // path below: the entry point and stack belong to user memory, `spawn_hook`
    // and `cleanup` are user functions that must *not* run in M-mode, and
    // `SpawnArgs` itself has to be read through the caller's page table.
    #[cfg(target_arch = "riscv64")]
    if crate::vfs::uptr::in_user_space() {
        return create_user_thread(spawn_args_ptr);
    }
    if spawn_args_ptr.is_null() {
        return -1;
    }
    let spawn_args = unsafe {&*spawn_args_ptr};
    let Some(stack) = Stack::from_raw(spawn_args.stack_start, spawn_args.stack_size) else {
        return -1;
    };
    let t = Builder::new(Entry::Posix(spawn_args.entry, spawn_args.arg))
                .set_stack(stack)
                .build();
    if let Some(cleanup) = spawn_args.cleanup {
        t.lock().set_cleanup(Entry::Posix(cleanup, spawn_args.arg));
    };
    // Link the new thread to the caller's process so that it shares the
    // caller's per-process fd table (stdin/stdout/stderr and any open files).
    // Without this, `current_process()` resolves to `None` on the new thread
    // and every VFS syscall returns `-EBADF` — i.e. the thread has no I/O.
    // `add_thread` takes the thread by value, so clone the `Arc` here; the
    // original `t` is still queued below.
    match crate::process::current_process() {
        Some(proc) => {
            if !proc.add_thread(t.clone()) {
                log::warn!(
                    "create_thread: new thread not linked to process"
                );
            }
        }
        None => {
            log::warn!("create_thread: caller has no process; new thread will have no fd table");
        }
    }
    let handle = Thread::id(&t);
    if let Some(f) = spawn_args.spawn_hook { f(handle, spawn_args_ptr as *mut _); }
    let ok = scheduler::queue_ready_thread(thread::IDLE, t);
    // We don't increment the rc of the created thread since it's also
    // referenced by the global queue. When this thread is retired,
    // it's removed from the global queue.
    debug_assert_eq!(ok, Ok(()));
    // Same-width integer cast (usize -> c_long): c_long matches the pointer
    // width on every target of this repo (i64 on LP64, i32 on ILP32/cortex-m),
    // so it stays value-identical to the previous transmute, but safe.
    handle as c_long
});

/// Serve `create_thread()` for a U-mode caller (DF-17).
///
/// The new thread shares the caller's address space and descriptor table — it
/// is a thread of the same process, not a child process — but it starts in
/// U-mode at an address the caller chose. Three things differ from the
/// kernel-thread path above:
///
/// * `SpawnArgs` is read through `uptr`, so an address the caller does not own
///   is `EFAULT` instead of a privileged read of physical memory;
/// * `spawn_hook` and `cleanup` are caller-supplied function pointers. Calling
///   them here would run U-mode code in M-mode, so they are *not* called. The
///   user-side thread library registers its TCB at the new thread's entry;
/// * the first instruction is reached through `enter_user_from_frame`, which
///   restores a synthetic trap frame instead of starting an image: `a0` carries
///   `arg`, `sp` the top of the caller's stack, and `ra` the exit trampoline, so
///   a thread entry that simply returns retires that thread.
///
/// `tp` is left zero: a new thread has no TLS block until its library installs
/// one. That is the same contract pthread has — `pthread_create` runs a
/// trampoline that sets up TLS before calling the user routine.
#[cfg(target_arch = "riscv64")]
fn create_user_thread(spawn_args_ptr: *const SpawnArgs) -> c_long {
    use crate::arch::riscv::mmu::{satp_sv39, Perms};
    use crate::error::code::{EAGAIN, EFAULT, EINVAL, EPERM};

    // The mirror is defined with plain integers, not `SpawnArgs`' function
    // pointer types. A `extern "C" fn` field is non-null by contract, so reading
    // a zero into it is undefined behaviour and the null-entry check below
    // would be optimised away. Reading the raw words keeps the check meaningful.
    #[repr(C)]
    struct UserSpawnArgs {
        spawn_hook: usize,
        stack_start: usize,
        stack_size: usize,
        entry: usize,
        arg: usize,
        cleanup: usize,
    }

    let Some(proc) = crate::process::current_process() else {
        return EPERM.to_errno() as c_long;
    };
    let Some(root) = crate::user::current_root() else {
        return EPERM.to_errno() as c_long;
    };
    let args: UserSpawnArgs = match crate::vfs::uptr::read_struct(spawn_args_ptr as *const _) {
        Ok(a) => a,
        Err(e) => return e.to_errno() as c_long,
    };
    let entry = args.entry;
    if entry == 0 {
        return EINVAL.to_errno() as c_long;
    }
    let Some(stack_top) = (args.stack_start as usize).checked_add(args.stack_size) else {
        return EINVAL.to_errno() as c_long;
    };
    // rv64 expects a 16-byte aligned stack pointer, and a zero-sized stack has
    // no room for the first frame.
    if args.stack_size < 16 || stack_top % 16 != 0 {
        return EINVAL.to_errno() as c_long;
    }
    // Prove the top of the stack is writable *in this address space* before
    // another thread is handed it. This demand-pages the page, so a stack
    // carved out of a fresh `mmap` works, while an address in a hole is refused
    // here rather than as a fault on another hart.
    if !crate::user::fault_in_range(stack_top - 16, 16, Perms::WRITE) {
        return EFAULT.to_errno() as c_long;
    }

    let satp = satp_sv39(root);
    let mut frame = crate::arch::riscv::Context::default();
    frame.mepc = entry;
    frame.mscratch = stack_top;
    frame.a0 = args.arg as usize;
    frame.ra = crate::user::THREAD_EXIT_TRAMPOLINE_VA;
    let body = Box::new(move || unsafe {
        crate::arch::riscv::enter_user_from_frame(&frame, satp)
    });
    let node = Builder::new(Entry::Closure(body)).build();
    if !proc.add_thread(node.clone()) {
        return EAGAIN.to_errno() as c_long;
    }
    let handle = Thread::id(&node);
    if crate::scheduler::queue_ready_thread(thread::IDLE, node).is_err() {
        return EAGAIN.to_errno() as c_long;
    }
    handle as c_long
}

define_syscall_handler!(
atomic_wait(addr: usize, val: usize, timeout: *const timespec) -> c_long {
    if addr == 0 {
        return -1;
    }
    let timeout = if timeout.is_null() {
        Tick::MAX
    } else {
        let timeout = unsafe { &*timeout };
        time::Tick::from_millis((timeout.tv_sec * 1000 + (timeout.tv_nsec as i64) / 1000000) as u64)
    };
    let ptr = addr as *const AtomicUsize;
    let atom = unsafe { &*ptr };
    futex::atomic_wait(atom, val, timeout).map_or_else(|e|e.to_errno() as c_long, |_| 0)
});

define_syscall_handler!(
atomic_wake(addr: usize, count: *mut usize) -> c_long {
    if addr == 0 {
        return -1;
    }
    let how_many = unsafe { *count };
    let ptr = addr as *const AtomicUsize;
    let atom = unsafe { &*ptr };
    futex::atomic_wake(atom, how_many).map_or_else(|_| -1, |woken| {
        unsafe { *count = woken };
        0
    })
});

define_syscall_handler!(
    clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> c_long {
    posix_timers::clock_gettime(clk_id, tp) as c_long
});

define_syscall_handler!(
    clock_settime(clk_id: clockid_t, tp: *const timespec) -> c_long {
    posix_timers::clock_settime(clk_id, tp) as c_long
});

define_syscall_handler!(
    timer_create(clock_id: clockid_t, evp: *const sigevent, timerid: *mut timer_t) -> c_long {
    posix_timers::timer_create(clock_id, evp, timerid) as c_long
});

define_syscall_handler!(
    timer_delete(timerid: timer_t) -> c_long {
    posix_timers::timer_delete(timerid) as c_long
});

define_syscall_handler!(
    timer_gettime(timerid: timer_t, value: *mut itimerspec) -> c_long {
    posix_timers::timer_gettime(timerid, value) as c_long
});

define_syscall_handler!(
    timer_settime(
        timerid: timer_t,
        flags: c_int,
        value: *const itimerspec,
        ovalue: *mut itimerspec
    ) -> c_long {
        posix_timers::timer_settime(timerid, flags, value, ovalue) as c_long
});

define_syscall_handler!(
    timer_getoverrun(timerid: timer_t) -> c_long {
    posix_timers::timer_getoverrun(timerid) as c_long
});

define_syscall_handler!(
alloc_mem(ptr: *mut *mut c_void, size: usize, align: usize) -> c_long {
    if ptr.is_null() {
        return -1;
    }
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

// realloc has no way to discover the size of the block it is handed, so it
// cannot be composed out of AllocMem and FreeMem in user space. The Issue 8
// reallocarray() - and the ordinary realloc() it is built on - therefore needs
// one kernel entry point rather than a user-side shim.
define_syscall_handler!(
realloc_mem(ptr: *mut *mut c_void, old_ptr: *mut c_void, new_size: usize) -> c_long {
    if ptr.is_null() {
        return -1;
    }
    // realloc(NULL, n) is malloc(n) per the C standard.
    let addr = if old_ptr.is_null() {
        crate::allocator::malloc(new_size)
    } else {
        crate::allocator::realloc(old_ptr as *mut u8, new_size)
    };
    if addr.is_null() {
        return -1;
    }
    unsafe { ptr.write(addr as *mut c_void) };
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
    pipe(fds: *mut c_int, flags: c_int) -> c_int {
        vfs_syscalls::pipe(fds, flags)
    }
);

define_syscall_handler!(
    dup2(oldfd: c_int, newfd: c_int) -> c_int {
        vfs_syscalls::dup2(oldfd, newfd)
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
    rename(oldpath: *const c_char, newpath: *const c_char) -> c_int {
        vfs_syscalls::rename(oldpath, newpath)
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
    signalaction(signum: c_int, act: *const c_void, oact: *mut c_void) -> c_int {
        crate::signal::posix::syscalls::sigaction(signum, act, oact)
    }
);
define_syscall_handler!(
    signaltstack(ss: *const c_void, old_ss: *mut c_void) -> c_int {
        crate::signal::posix::syscalls::sigaltstack(ss, old_ss)
    }
);
define_syscall_handler!(
    sigpending(set: *mut libc::sigset_t) -> c_int {
        crate::signal::posix::syscalls::sigpending(set)
    }
);
define_syscall_handler!(
    sigprocmask(how: c_int, set: *const libc::sigset_t, oldset: *mut libc::sigset_t) -> c_int {
        crate::signal::posix::syscalls::sigprocmask(how, set, oldset)
    }
);
define_syscall_handler!(
    sigqueueinfo(_pid: c_int, _sig: c_int, _info: *const c_void) -> c_int {
        // POSIX lists `sigqueue()` as optional, and the kernel has no way to
        // deliver a value-carrying signal yet. Reporting ENOSYS is honest:
        // the caller learns the feature is absent instead of believing the
        // signal was queued.
        -libc::ENOSYS as c_int
    }
);
define_syscall_handler!(
    sigsuspend(set: *const libc::sigset_t) -> c_int {
        crate::signal::posix::syscalls::sigsuspend(set)
    }
);
define_syscall_handler!(
    sigtimedwait(set: *const sigset_t, info: *mut c_void, timeout: *const timespec) -> c_int {
        crate::signal::posix::syscalls::sigtimedwait(set, info, timeout)
    }
);
define_syscall_handler!(
    kill(pid: libc::pid_t, sig: c_int) -> c_int {
        crate::signal::posix::syscalls::kill(pid, sig)
    }
);
define_syscall_handler!(
    raise(sig: c_int) -> c_int {
        crate::signal::posix::syscalls::raise(sig)
    }
);
define_syscall_handler!(
    sigwait(set: *const libc::sigset_t, sig: *mut c_int) -> c_int {
        crate::signal::posix::syscalls::sigwait(set, sig)
    }
);

// POSIX I/O multiplexing. `nfds` is `nfds_t` (`unsigned int`) on the C side;
// it arrives zero-extended, so it is read as `usize` and range-checked
// against `POLL_NFDS_MAX`.
define_syscall_handler!(
    poll(fds: *mut c_void, nfds: usize, timeout: c_int) -> core::ffi::c_long {
        vfs_syscalls::poll(fds, nfds, timeout)
    }
);
define_syscall_handler!(
    ppoll(fds: *mut c_void, nfds: usize, timeout: *const timespec, sigmask: *const sigset_t) -> core::ffi::c_long {
        vfs_syscalls::ppoll(fds, nfds, timeout, sigmask)
    }
);
define_syscall_handler!(
    select(nfds: c_int, readfds: *mut c_void, writefds: *mut c_void, exceptfds: *mut c_void, timeout: *mut libc::timeval) -> c_int {
        vfs_syscalls::select(nfds, readfds, writefds, exceptfds, timeout)
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
        net_syscalls::accept(sockfd, addr, len)
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
    clock_nanosleep(
        clock_id: clockid_t,
        flags: c_int,
        rqtp: *const timespec,
        rmtp: *mut timespec
    ) -> c_long {
        posix_timers::clock_nanosleep(clock_id, flags, rqtp, rmtp) as c_long
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

define_syscall_handler!(
    ioctl(fd: c_int, request: c_ulong, out: *mut core::ffi::c_void) -> c_int {
        vfs_syscalls::ioctl(fd, request as core::ffi::c_ulong, out)
    }
);

// ---------------------------------------------------------------------------
// POSIX process model
//
// Split in two: the handlers here only unwrap the ABI argument types, and
// `proc_syscalls` below decides what the call means on a target that has no
// user/kernel split. Keeping the `cfg` in one place means the table does not
// need a `cfg` per entry, and a 32-bit board still gets an honest `ENOSYS`
// rather than a call that silently does nothing.
// ---------------------------------------------------------------------------

mod proc_syscalls {
    //! Bodies of the process-model syscalls, gated on there being a U-mode.
    use super::{c_char, c_int};

    #[cfg(target_arch = "riscv64")]
    pub fn getpid() -> isize {
        crate::user::sys_getpid()
    }

    #[cfg(target_arch = "riscv64")]
    pub fn getppid() -> isize {
        crate::user::sys_getppid()
    }

    /// `fork` is the one call that needs the trap frame: the child must resume
    /// with the parent's registers, and they exist nowhere else.
    #[cfg(target_arch = "riscv64")]
    pub fn fork(frame: usize) -> isize {
        let frame = frame as *const crate::arch::riscv::Context;
        if frame.is_null() {
            return crate::error::code::EPERM.to_errno() as isize;
        }
        // SAFETY: the frame pointer came from the trap entry for *this* syscall
        // and is live for the duration of the dispatch.
        unsafe { crate::user::fork(&*frame) }
    }

    #[cfg(target_arch = "riscv64")]
    pub fn execve(
        path: *const c_char,
        argv: *const *const c_char,
        envp: *const *const c_char,
    ) -> isize {
        crate::user::sys_execve(path, argv, envp)
    }

    #[cfg(target_arch = "riscv64")]
    pub fn waitpid(pid: c_int, status: *mut c_int, options: c_int) -> isize {
        crate::user::sys_waitpid(pid, status, options)
    }

    #[cfg(target_arch = "riscv64")]
    pub fn exit_group(status: c_int) -> isize {
        crate::user::sys_exit_group(status)
    }

    #[cfg(target_arch = "riscv64")]
    pub fn mmap(
        addr: usize,
        len: usize,
        prot: usize,
        flags: usize,
        fd: c_int,
        off: usize,
    ) -> isize {
        crate::user::sys_mmap(addr, len, prot, flags, fd, off)
    }

    #[cfg(target_arch = "riscv64")]
    pub fn munmap(addr: usize, len: usize) -> isize {
        crate::user::sys_munmap(addr, len)
    }

    // --- targets without a user address space ---

    #[cfg(not(target_arch = "riscv64"))]
    mod nosys {
        macro_rules! enosys {
            ($($name:ident($($arg:ty),*) -> $ret:ty;)*) => {
                $(
                    pub fn $name($(_: $arg),*) -> $ret {
                        crate::error::code::ENOSYS.to_errno() as $ret
                    }
                )*
            };
        }
        // Types only: the macro takes `$arg:ty`, so the parameters are unnamed
        // in the source and bound to `_` in the expansion.
        enosys! {
            getpid() -> isize;
            getppid() -> isize;
            fork(usize) -> isize;
            execve(*const core::ffi::c_char, *const *const core::ffi::c_char, *const *const core::ffi::c_char) -> isize;
            waitpid(core::ffi::c_int, *mut core::ffi::c_int, core::ffi::c_int) -> isize;
            exit_group(core::ffi::c_int) -> isize;
            mmap(usize, usize, usize, usize, core::ffi::c_int, usize) -> isize;
            munmap(usize, usize) -> isize;
        }
    }

    #[cfg(not(target_arch = "riscv64"))]
    pub use nosys::*;
}

define_syscall_handler!(get_pid() -> isize {
    proc_syscalls::getpid()
});

define_syscall_handler!(get_ppid() -> isize {
    proc_syscalls::getppid()
});

define_syscall_handler!(waitpid(pid: c_int, status: *mut c_int, options: c_int) -> isize {
    proc_syscalls::waitpid(pid, status, options)
});

define_syscall_handler!(exit_group(status: c_int) -> isize {
    proc_syscalls::exit_group(status)
});

define_syscall_handler!(
    mmap(addr: usize, len: usize, prot: usize, flags: usize, fd: c_int, off: usize) -> isize {
        proc_syscalls::mmap(addr, len, prot, flags, fd, off)
    }
);

define_syscall_handler!(munmap(addr: usize, len: usize) -> isize {
    proc_syscalls::munmap(addr, len)
});

/// `fork(2)`. Hand-written rather than generated because the frame pointer is
/// not one of the six argument registers.
pub mod fork {
    use super::*;

    pub fn handle_context(ctx: &Context) -> usize {
        proc_syscalls::fork(ctx.frame) as usize
    }
}

/// `sigreturn(2)`. Not a user-callable API: the trampoline page issues it
/// after a signal handler returns. The frame has to be read from user memory,
/// so it goes through the architecture frame pointer rather than the argument
/// registers, exactly like `fork`.
pub mod sigreturn {
    use super::*;

    pub fn handle_context(ctx: &Context) -> usize {
        #[cfg(target_arch = "riscv64")]
        {
            crate::signal::delivery::sigreturn(
                ctx.frame as *mut crate::arch::riscv::Context,
            ) as usize
        }
        #[cfg(not(target_arch = "riscv64"))]
        {
            let _ = ctx;
            -libc::ENOSYS as isize as usize
        }
    }
}

/// `execve(2)`. Three pointer arguments, all of which need translating before
/// the kernel may look at them.
pub mod execve {
    use super::*;

    pub fn handle_context(ctx: &Context) -> usize {
        let args = &ctx.args;
        proc_syscalls::execve(
            args[0] as *const c_char,
            args[1] as *const *const c_char,
            args[2] as *const *const c_char,
        ) as usize
    }
}

#[cfg(enable_syscall)]
syscall_table! {
    (Echo, echo),
    (Nop, nop),
    (GetTid, get_tid),
    (GetSchedParam, get_sched_param),
    (SetSchedParam, set_sched_param),
    (CreateThread, create_thread),
    (ExitThread, exit_thread),
    (AtomicWake, atomic_wake),
    (AtomicWait, atomic_wait),
    // For test only
    (ClockGetTime, clock_gettime),
    (ClockSetTime, clock_settime),
    (ClockNanoSleep, clock_nanosleep),
    (TimerCreate, timer_create),
    (TimerDelete, timer_delete),
    (TimerGetTime, timer_gettime),
    (TimerSetTime, timer_settime),
    (TimerGetOverrun, timer_getoverrun),
    (AllocMem, alloc_mem),
    (FreeMem, free_mem),
    (ReallocMem, realloc_mem),
    (Write, write),
    (Close, close),
    (Read, read),
    (Open, open),
    (Lseek, lseek),
    (SchedYield, sched_yield),
    (Rmdir, rmdir),
    (Link, link),
    (Unlink, unlink),
    (Rename, rename),
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
    (MqOpen, mq_open),
    (MqClose, mq_close),
    (MqUnlink, mq_unlink),
    (MqTimedSend, mq_timedsend),
    (MqTimedReceive, mq_timedreceive),
    (MqGetSetAttr, mq_getsetattr),
    (Ioctl, ioctl),
    (Kill, kill),
    (Raise, raise),
    (SigWait, sigwait),
    (Poll, poll),
    (PPoll, ppoll),
    (Select, select),
    (SigReturn, sigreturn),
    (Fork, fork),
    (Execve, execve),
    (WaitPid, waitpid),
    (ExitGroup, exit_group),
    (GetPid, get_pid),
    (GetPpid, get_ppid),
    (MMap, mmap),
    (MUnmap, munmap),
    (Pipe, pipe),
    (Dup2, dup2),
}

#[cfg(not(enable_syscall))]
pub fn dispatch_syscall(ctx: &Context) -> usize {
    0
}

// Begin syscall modules.
pub mod echo;
pub mod posix_timers;
// End syscall modules.
