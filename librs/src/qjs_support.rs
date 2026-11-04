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

// QuickJS front-end support syscalls.
//
// The QuickJS shell is linked as a plain C `app_entry` executable against the
// toolchain's newlib (libc.a) plus the librs newlib-adapter staticlib — there
// is no Rust `std`. newlib's libc.a already supplies some POSIX wrappers built
// on the underscore stubs in `syscalls.rs`, and quickjs-libc.c/qjs.c
// additionally need the symbols below. They are split into:
//   (a) routed to the kernel via bk_syscall! where an NR exists, and
//   (b) ENOSYS/unsupported stubs for features the kernel does not have
//       (dynamic loading, env mutation, and the exec/shell family
//        execvp/execvpe/system/popen/pclose — the kernel has no PATH search
//        and no shell to hand a command to).
//       `tcgetattr`/`tcsetattr` are not in this group: they translate newlib's
//       `termios` to the kernel's and go through `TCGETS`/`TCSETS`.
// The stubs let quickjs-libc.c link unconditionally; the live check/eval path
// never calls them.
//
// Coverage note: these `#[no_mangle]` symbols are QuickJS-specific C exports
// and are intentionally *outside* the four-layer POSIX audit
// (tools/posix_audit.py only inspects librs/src/syscall/blueos/mod.rs). The
// process-creation trio `fork`/`execve`/`waitpid` is NOT here: those are wired
// through the main blueos backend and covered by that audit. The
// ENOSYS stubs below are honest "unsupported" answers, not silent no-ops: each
// sets errno and returns -1 / NULL so a qjs program fails loudly rather than
// misbehaving.

use blueos_header::syscalls::NR::{
    Chdir, ClockGetTime, ClockNanoSleep, Fcntl, GetDents, Getcwd, Link, Mkdir, Rmdir, SchedYield,
    Stat, Unlink,
};
use blueos_scal::bk_syscall;
use libc::{
    c_char, c_int, c_ulong, c_void, clockid_t, mode_t, off_t, size_t, ssize_t, timespec, ENOSYS,
};
use crate::syscall::{Sys, Syscall};

// The kernel-routed underscore stubs (_open/_read/_write/_close/...) and the
// CLOCK_* kernel clock-id constants live in syscalls.rs (the generic newlib
// adapter). This front-end file builds the QuickJS POSIX surface on top of
// them; both modules are compiled into the same newlib.rs crate root.
use crate::c_clock_id::KERNEL_MONOTONIC;
use crate::syscalls::{
    _close, _fstat, _getpid, _kill, _lseek, _open, _read, _write,
};

// errno lives in the reentrant struct provided by syncs.rs (same crate).
use crate::syncs::__getreent;

/// Set the C library `errno` for the current thread and return -1, the
/// universal "syscall failed" convention newlib expects. newlib keeps `errno`
/// in the reentrant structure (`_REENT->_errno`, the first field); `__getreent`
/// is provided by syncs.rs in this same crate.
#[inline]
unsafe fn fail(errno: c_int) -> c_int {
    let reent = unsafe { __getreent() };
    if !reent.is_null() {
        unsafe { (*reent)._errno = errno };
    }
    -1
}

// -- routed to the kernel --------------------------------------------------
//
// The underscore syscall bodies below route to the kernel via bk_syscall!.
// _open/_read/_write/_close/_lseek/_fstat/_getpid/_kill are defined in
// syscalls.rs (the generic adapter) and imported above; the rest are
// QuickJS-specific and defined here.

#[no_mangle]
pub unsafe extern "C" fn _chdir(path: *const c_char) -> c_int {
    bk_syscall!(Chdir, path) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _stat(path: *const c_char, st: *mut c_void) -> c_int {
    bk_syscall!(Stat, path, st as *mut c_char) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _mkdir(path: *const c_char, mode: mode_t) -> c_int {
    bk_syscall!(Mkdir, path, mode) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _rmdir(path: *const c_char) -> c_int {
    bk_syscall!(Rmdir, path) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _unlink(path: *const c_char) -> c_int {
    bk_syscall!(Unlink, path) as c_int
}

#[no_mangle]
pub unsafe extern "C" fn _getcwd(buf: *mut c_char, size: size_t) -> *mut c_char {
    let rc = bk_syscall!(Getcwd, buf, size) as c_int;
    if rc != 0 {
        return core::ptr::null_mut();
    }
    buf
}

#[no_mangle]
pub unsafe extern "C" fn _fcntl(fd: c_int, cmd: c_int, arg: c_int) -> c_int {
    bk_syscall!(Fcntl, fd, cmd, arg as usize) as c_int
}

// newlib's close() wrapper calls _close; quickjs-libc's js_free_message_pipe
// calls the non-underscore close() directly.
#[no_mangle]
pub unsafe extern "C" fn close(fd: c_int) -> c_int {
    _close(fd)
}

// newlib's exit() calls _exit() at the end. On this embedded single-process
// target there is nowhere to exit to; park the thread forever (qjs's main
// returns through exit() when the REPL quits).
#[no_mangle]
pub unsafe extern "C" fn _exit(_code: c_int) -> ! {
    loop {
        bk_syscall!(SchedYield);
    }
}

// quickjs.c's js__hrtime_ns (cutils.h) and quickjs-libc.c call clock_gettime
// directly. Route it to the kernel clock syscall, translating the toolchain's
// clock id (newlib: CLOCK_REALTIME=1, CLOCK_MONOTONIC=4) into the kernel's
// (0 and 1) - see c_clock_id.rs. Passing the raw id would make REALTIME read
// the monotonic clock and MONOTONIC fail with EINVAL.
#[no_mangle]
pub unsafe extern "C" fn clock_gettime(clock_id: clockid_t, tp: *mut timespec) -> c_int {
    if tp.is_null() {
        return fail(libc::EFAULT);
    }
    let Some(kernel_id) = crate::c_clock_id::from_c(clock_id) else {
        return fail(libc::EINVAL);
    };
    bk_syscall!(ClockGetTime, kernel_id, tp) as c_int
}

// -- terminal line discipline ----------------------------------------------

/// Mirror of the kernel's `Termios` (`kernel/kernel/src/devices/tty/termios.rs`):
/// four 32-bit flag words, twelve control characters, then the two baud fields.
/// It is not newlib's `struct termios`, which has `c_line` in front of a
/// 32-byte `c_cc`, so the ioctl cannot write straight into the caller's buffer.
#[repr(C)]
#[derive(Clone, Copy)]
struct KernelTermios {
    c_iflag: u32,
    c_oflag: u32,
    c_cflag: u32,
    c_lflag: u32,
    c_cc: [u8; 12],
    ispeed: u32,
    ospeed: u32,
}

const _: () = assert!(core::mem::size_of::<KernelTermios>() == 36);
const _: () = assert!(libc::NCCS >= 12);

fn kernel_to_newlib(src: &KernelTermios, dst: &mut libc::termios) {
    dst.c_iflag = src.c_iflag;
    dst.c_oflag = src.c_oflag;
    dst.c_cflag = src.c_cflag;
    dst.c_lflag = src.c_lflag;
    // newlib keeps a `c_line` byte between the flags and `c_cc`; the kernel's
    // line discipline has no such field.
    dst.c_line = 0;
    dst.c_cc = [0; libc::NCCS];
    dst.c_cc[..src.c_cc.len()].copy_from_slice(&src.c_cc);
}

fn newlib_to_kernel(src: &libc::termios, dst: &mut KernelTermios) {
    dst.c_iflag = src.c_iflag;
    dst.c_oflag = src.c_oflag;
    dst.c_cflag = src.c_cflag;
    dst.c_lflag = src.c_lflag;
    dst.c_cc.copy_from_slice(&src.c_cc[..12]);
}

// newlib's `<termios.h>` values for the `action` argument of `tcsetattr()`.
const TCSANOW: c_int = 0;
const TCSADRAIN: c_int = 1;
const TCSAFLUSH: c_int = 2;

#[no_mangle]
pub unsafe extern "C" fn tcgetattr(fd: c_int, termios_p: *mut libc::termios) -> c_int {
    if termios_p.is_null() {
        return fail(libc::EFAULT);
    }
    // Zero-initialised: the kernel fills the whole struct on success, and the
    // baud fields are not part of newlib's view.
    let mut k = unsafe { core::mem::zeroed::<KernelTermios>() };
    match unsafe {
        Sys::ioctl(
            fd,
            libc::TCGETS as c_ulong,
            &mut k as *mut KernelTermios as *mut c_void,
        )
    } {
        Ok(_) => {
            unsafe { kernel_to_newlib(&k, &mut *termios_p) };
            0
        }
        Err(errno) => fail(errno.0),
    }
}

#[no_mangle]
pub unsafe extern "C" fn tcsetattr(
    fd: c_int,
    action: c_int,
    termios_p: *const libc::termios,
) -> c_int {
    if termios_p.is_null() {
        return fail(libc::EFAULT);
    }
    let request = match action {
        TCSANOW => libc::TCSETS,
        TCSADRAIN => libc::TCSETSW,
        TCSAFLUSH => libc::TCSETSF,
        _ => return fail(libc::EINVAL),
    };
    // Read-modify-write: newlib's struct has no baud fields, so fetch the
    // current rate instead of driving the UART to zero baud.
    let mut k = unsafe { core::mem::zeroed::<KernelTermios>() };
    if let Err(errno) = unsafe {
        Sys::ioctl(
            fd,
            libc::TCGETS as c_ulong,
            &mut k as *mut KernelTermios as *mut c_void,
        )
    } {
        return fail(errno.0);
    }
    unsafe { newlib_to_kernel(&*termios_p, &mut k) };
    match unsafe {
        Sys::ioctl(
            fd,
            request as c_ulong,
            &mut k as *mut KernelTermios as *mut c_void,
        )
    } {
        Ok(_) => 0,
        Err(errno) => fail(errno.0),
    }
}

// `poll()` is a real POSIX call now and lives in `src/poll.rs`, next to
// `ppoll()`. It used to be a stub here that reported the console as always
// readable; that fooled the REPL into running, but it also meant any program
// that polled a socket never saw it become ready.

#[no_mangle]
pub unsafe extern "C" fn select(
    _nfds: c_int,
    _readfds: *mut c_void,
    _writefds: *mut c_void,
    _exceptfds: *mut c_void,
    _timeout: *mut c_void,
) -> c_int {
    fail(ENOSYS)
}

// Process creation / management. `fork`, `waitpid` and `execve` are provided by
// `unistd` as real wrappers now that the kernel has a process model; keep the
// path-searching variants (`execvp`/`execvpe`) and `system` here as ENOSYS,
// since the kernel does not search PATH and has no shell to hand a command to.
#[no_mangle]
pub unsafe extern "C" fn execvp(_file: *const c_char, _argv: *const *const c_char) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn execvpe(
    _file: *const c_char,
    _argv: *const *const c_char,
    _envp: *const *const c_char,
) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn system(_command: *const c_char) -> c_int {
    fail(ENOSYS)
}

// Dynamic loading: no dlopen on a statically-linked embedded image. quickjs-libc
// only uses these for native modules, which we never load.
#[no_mangle]
pub unsafe extern "C" fn dlopen(_filename: *const c_char, _flags: c_int) -> *mut c_void {
    fail(ENOSYS);
    core::ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn dlsym(_handle: *mut c_void, _symbol: *const c_char) -> *mut c_void {
    core::ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn dlclose(_handle: *mut c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn dlerror() -> *const c_char {
    b"dynamic loading not supported\0".as_ptr() as *const c_char
}

// Environment mutation: there is no environ store in the kernel; getenv (from
// libc.a) already returns NULL for everything, so set/unset are no-ops.
#[no_mangle]
pub unsafe extern "C" fn setenv(
    _name: *const c_char,
    _value: *const c_char,
    _overwrite: c_int,
) -> c_int {
    0
}

#[no_mangle]
pub unsafe extern "C" fn unsetenv(_name: *const c_char) -> c_int {
    0
}

// `dup()` is `fcntl(oldfd, F_DUPFD, 0)`; the kernel's per-process descriptor
// table owns the duplication, so this only has to forward the call. The new
// descriptor shares the open file description (and therefore the offset).
#[no_mangle]
pub unsafe extern "C" fn dup(oldfd: c_int) -> c_int {
    const F_DUPFD: c_int = 0;
    unsafe { bk_syscall!(Fcntl, oldfd, F_DUPFD, 0usize) as c_int }
}

// `dup2()` replaces the target descriptor, which only the kernel's fd table
// can do atomically; `F_DUPFD` alone cannot clear the old occupant.
#[no_mangle]
pub unsafe extern "C" fn dup2(oldfd: c_int, newfd: c_int) -> c_int {
    unsafe { bk_syscall!(Dup2, oldfd, newfd) as c_int }
}

// `pipe()` leaves both ends blocking and without `FD_CLOEXEC`, which is the
// flags=0 form of the kernel's pipe call.
#[no_mangle]
pub unsafe extern "C" fn pipe(pipefd: *mut c_int) -> c_int {
    unsafe { bk_syscall!(Pipe, pipefd, 0usize) as c_int }
}

// ---------------------------------------------------------------------------
// App-facing POSIX surface
//
// The QuickJS app links the *full* quickjs-libc.c (std/os/worker modules),
// which references the whole POSIX syscall surface even though the live path
// only touches the console (read/write/poll/termios) and the clock. The
// toolchain's newlib libc.a is bare for this target — it does NOT provide the
// non-underscore POSIX wrappers (open/read/stat/mkdir/...) — so every one of
// these must resolve here. They split into:
//   (a) thin wrappers over the kernel-routed underscore stubs, and
//   (b) ENOSYS stubs for kernel-unsupported features (popen, symlink, uid/gid,
//       getrusage, execve). These live in code the app never executes
//       (os.exec, os.symlink, Worker, ...); they only need to link.
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn open(path: *const c_char, flags: c_int, mode: c_int) -> c_int {
    _open(path as *const u8, flags, mode)
}

#[no_mangle]
pub unsafe extern "C" fn read(fd: c_int, buf: *mut c_void, len: size_t) -> ssize_t {
    _read(fd, buf, len)
}

#[no_mangle]
pub unsafe extern "C" fn write(fd: c_int, buf: *const c_void, len: size_t) -> ssize_t {
    _write(fd, buf, len)
}

#[no_mangle]
pub unsafe extern "C" fn lseek(fd: c_int, offset: off_t, whence: c_int) -> off_t {
    _lseek(fd, offset, whence)
}

#[no_mangle]
pub unsafe extern "C" fn fstat(fd: c_int, st: *mut c_void) -> c_int {
    _fstat(fd, st)
}

#[no_mangle]
pub unsafe extern "C" fn stat(path: *const c_char, st: *mut c_void) -> c_int {
    _stat(path, st)
}

#[no_mangle]
pub unsafe extern "C" fn lstat(path: *const c_char, st: *mut c_void) -> c_int {
    // No symlink support; lstat is stat for our purposes.
    _stat(path, st)
}

#[no_mangle]
pub unsafe extern "C" fn chdir(path: *const c_char) -> c_int {
    _chdir(path)
}

#[no_mangle]
pub unsafe extern "C" fn mkdir(path: *const c_char, mode: mode_t) -> c_int {
    _mkdir(path, mode)
}

#[no_mangle]
pub unsafe extern "C" fn kill(pid: c_int, sig: c_int) -> c_int {
    _kill(pid, sig)
}

#[no_mangle]
pub unsafe extern "C" fn getdents(fd: c_int, buf: *mut c_char, size: size_t) -> ssize_t {
    bk_syscall!(GetDents, fd, buf as *mut c_void, size) as ssize_t
}

#[no_mangle]
pub unsafe extern "C" fn _link(oldpath: *const c_char, newpath: *const c_char) -> c_int {
    bk_syscall!(Link, oldpath, newpath) as c_int
}

// Strong nanosleep for the QuickJS app.
//
// POSIX defines `nanosleep` in terms of `CLOCK_REALTIME`, but the historical
// behaviour - and what every real implementation does - is to sleep on the
// monotonic clock, so a wall-clock adjustment cannot shorten or extend a
// sleep. This passes the kernel's monotonic id directly, which is why it does
// not go through `c_clock_id::from_c`: there is no C-visible clock id to
// translate here.
#[no_mangle]
pub unsafe extern "C" fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> c_int {
    if rqtp.is_null() {
        return fail(libc::EFAULT);
    }
    bk_syscall!(ClockNanoSleep, KERNEL_MONOTONIC, 0 as c_int, rqtp, rmtp) as c_int
}

// -- ENOSYS stubs for kernel-unsupported features (dead code in the app) -----

#[no_mangle]
pub unsafe extern "C" fn ioctl(_fd: c_int, _request: usize, _arg: *mut c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn popen(_command: *const c_char, _mode: *const c_char) -> *mut c_void {
    fail(ENOSYS);
    core::ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn pclose(_stream: *mut c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn realpath(_path: *const c_char, _resolved: *mut c_char) -> *mut c_char {
    fail(ENOSYS);
    core::ptr::null_mut()
}

#[no_mangle]
pub unsafe extern "C" fn readlink(
    _path: *const c_char,
    _buf: *mut c_char,
    _bufsize: size_t,
) -> ssize_t {
    fail(ENOSYS) as ssize_t
}

#[no_mangle]
pub unsafe extern "C" fn symlink(_target: *const c_char, _linkpath: *const c_char) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn utimes(_path: *const c_char, _times: *const c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn getrusage(_who: c_int, _usage: *mut c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn _times(_buf: *mut c_void) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn setuid(_uid: c_int) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn setgid(_gid: c_int) -> c_int {
    fail(ENOSYS)
}

#[no_mangle]
pub unsafe extern "C" fn setgroups(_ngroups: c_int, _gidset: *const c_int) -> c_int {
    fail(ENOSYS)
}

// quickjs-libc's js_std_urlGet / worker code queries the page size.
#[no_mangle]
pub extern "C" fn sysconf(name: c_int) -> i64 {
    const SC_PAGESIZE: c_int = 30;
    const SC_NPROCESSORS_ONLN: c_int = 84;
    match name {
        SC_PAGESIZE => 4096,
        SC_NPROCESSORS_ONLN => 1,
        _ => -1,
    }
}

// ---------------------------------------------------------------------------
// 64-bit software atomic builtins (__atomic_*_8)
//
// thumbv8m.main (Cortex-M33/M55) has no native 64-bit atomic instructions, so
// GCC lowers 64-bit `__atomic_*` operations in the QuickJS engine's C sources
// (`js_atomics_op`, `js_atomics_store`, ... via quickjs-c-atomics.h) into these
// compiler-rt libcalls. libgcc.a does not provide the 8-byte variants for this
// ABI, so we implement them here.
//
// Each operation is serialized by masking local interrupts for the duration of
// the 8-byte load/modify/store, giving the required atomicity on this
// single-core target. This matches how the kernel guards its own shared state
// (blueos::arch::disable_local_irq_save / enable_local_irq_restore, the BASEPRI
// irqsave pair).
// ---------------------------------------------------------------------------

/// Run `f` with local interrupts masked, returning its result.
#[inline(always)]
fn with_irq_masked<R>(f: impl FnOnce() -> R) -> R {
    let saved = blueos::arch::disable_local_irq_save();
    let r = f();
    blueos::arch::enable_local_irq_restore(saved);
    r
}

/// Atomic 8-byte load. `ptr` must be valid for an 8-byte read.
#[no_mangle]
pub unsafe extern "C" fn __atomic_load_8(ptr: *const u64, _order: c_int) -> u64 {
    with_irq_masked(|| unsafe { core::ptr::read_volatile(ptr) })
}

/// Atomic 8-byte store. `ptr` must be valid for an 8-byte write.
#[no_mangle]
pub unsafe extern "C" fn __atomic_store_8(ptr: *mut u64, val: u64, _order: c_int) {
    with_irq_masked(|| unsafe { core::ptr::write_volatile(ptr, val) })
}

/// Atomic 8-byte exchange; returns the previous value.
#[no_mangle]
pub unsafe extern "C" fn __atomic_exchange_8(ptr: *mut u64, val: u64, _order: c_int) -> u64 {
    with_irq_masked(|| unsafe {
        let old = core::ptr::read_volatile(ptr);
        core::ptr::write_volatile(ptr, val);
        old
    })
}

/// Atomic 8-byte compare-and-exchange. On success stores `desired` into `*ptr`
/// and returns 1; on failure stores the current value into `*expected` and
/// returns 0.
#[no_mangle]
pub unsafe extern "C" fn __atomic_compare_exchange_8(
    ptr: *mut u64,
    expected: *mut u64,
    desired: u64,
    _weak: c_int,
    _success_order: c_int,
    _failure_order: c_int,
) -> u8 {
    with_irq_masked(|| unsafe {
        let old = core::ptr::read_volatile(ptr);
        if old == core::ptr::read_volatile(expected) {
            core::ptr::write_volatile(ptr, desired);
            1
        } else {
            core::ptr::write_volatile(expected, old);
            0
        }
    })
}

macro_rules! atomic_fetch_op_8 {
    ($name:ident, $op:tt) => {
        /// Atomic 8-byte fetch-and-op; returns the previous value.
        #[no_mangle]
        pub unsafe extern "C" fn $name(ptr: *mut u64, val: u64, _order: c_int) -> u64 {
            with_irq_masked(|| unsafe {
                let old = core::ptr::read_volatile(ptr);
                core::ptr::write_volatile(ptr, old $op val);
                old
            })
        }
    };
}

atomic_fetch_op_8!(__atomic_fetch_add_8, +);
atomic_fetch_op_8!(__atomic_fetch_sub_8, -);
atomic_fetch_op_8!(__atomic_fetch_and_8, &);
atomic_fetch_op_8!(__atomic_fetch_or_8, |);
atomic_fetch_op_8!(__atomic_fetch_xor_8, ^);
