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

use super::Syscall;
use crate::{
    c_str::CStr,
    errno::{Errno, Result},
    mqueue::mq_attr,
};
use blueos_header::syscalls::NR::{
    Accept, Bind, Chdir, ClockGetTime, ClockNanoSleep, ClockSetTime, Close, Connect, Echo, Execve,
    ExitGroup, FStat, Fcntl, Fork, FStatfs, FreeAddrinfo, Ftruncate, GetAddrinfo, GetDents, Getcwd,
    GetPid, GetPpid, Getsockopt, Ioctl, Link, Listen, Lseek, MMap, MUnmap, Mkdir, MqClose,
    MqGetSetAttr, MqOpen, MqTimedReceive, MqTimedSend, MqUnlink, Open, Pipe, Read, Recv, Recvfrom,
    Recvmsg, Rename, Rmdir, SchedYield, Send, Sendmsg, Sendto, Setsockopt, Shutdown, Socket,
    Statfs, Unlink, WaitPid, Write,
};
use blueos_scal::bk_syscall;
use libc::{
    c_char, c_int, c_long, c_uint, c_ulong, c_void, clockid_t, dev_t, mode_t, msghdr, off_t,
    size_t, sockaddr, socklen_t, ssize_t, statvfs, timespec, utsname,
};

/// Fill one `struct utsname` field: NUL-terminated and clipped to the field's
/// length, leaving no stale bytes behind.
fn fill_utsname(field: &mut [c_char; 65], value: &str) {
    let n = value.len().min(field.len() - 1);
    for (slot, byte) in field.iter_mut().zip(value.bytes()).take(n) {
        *slot = byte as c_char;
    }
    field[n] = 0;
}

// convert value returned by syscall to user Result.
//
// A failing syscall reports the error as a negative errno. The errno is also
// stored in the thread's `errno` here, because that is what a C caller
// expects to find: the POSIX convention is that a function returning -1 has
// set `errno`. Storing it at the boundary means no call site can forget to,
// and the `Errno` value stays available for callers that want to inspect it
// without going through `errno`.
const ERRNO_MAX: usize = 4095;
pub fn to_result(result: usize) -> Result<usize> {
    if result > ERRNO_MAX.wrapping_neg() {
        let errno = result.wrapping_neg() as c_int;
        crate::errno::ERRNO.set(errno);
        Err(Errno(errno))
    } else {
        Ok(result)
    }
}
pub struct Sys;

impl Syscall for Sys {
    unsafe fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fildes: c_int,
        off: off_t,
    ) -> Result<*mut c_void> {
        // Only anonymous private/shared mappings exist: the kernel refuses a
        // file-backed request with EINVAL rather than handing back a mapping
        // that reads zeros (see `user::sys_mmap`). A thread with no address
        // space - every in-kernel thread, including the POSIX cases - gets
        // ENOMEM, which is the honest answer: there is nothing to map into.
        let mapped = bk_syscall!(
            MMap,
            addr,
            len,
            prot as usize,
            flags as usize,
            fildes,
            off as usize
        );
        to_result(mapped as usize).map(|base| base as *mut c_void)
    }

    unsafe fn munmap(addr: *mut c_void, len: usize) -> Result<()> {
        // Reported as a failure rather than swallowed: an `munmap` that
        // returned success for an address it never mapped would tell a caller
        // its memory was released when it was not. Without a user address
        // space the kernel answers EINVAL, which is what POSIX specifies for a
        // range that is not mapped.
        to_result(bk_syscall!(MUnmap, addr, len) as usize).map(|_| ())
    }

    fn echo(val: c_long) -> c_long {
        // Not a POSIX call: BlueOS's `Echo` returns its argument unchanged.
        // It exists so a test can prove the syscall path end to end (argument
        // register in, return register out) without a real device behind it.
        bk_syscall!(Echo, val) as c_long
    }

    fn get_pid() -> c_int {
        // The kernel returns the current process id; it cannot fail, and a
        // thread with no process gets 0 - which is exactly what the C `getpid`
        // returned before processes existed, so existing callers keep working.
        bk_syscall!(GetPid) as c_int
    }

    fn get_ppid() -> c_int {
        // 0 at the root process, whose creator does not exist.
        bk_syscall!(GetPpid) as c_int
    }

    unsafe fn wait_pid(pid: c_int, status: *mut c_int, options: c_int) -> Result<c_int> {
        // `status` is written by the kernel through the uptr layer, so it is
        // safe to pass a user pointer here; the call returns the reaped child's
        // pid, or a negative errno (ECHILD when there is nothing to collect).
        to_result(bk_syscall!(WaitPid, pid, status, options) as usize).map(|r| r as c_int)
    }

    fn exit_group(status: c_int) -> c_int {
        // On success this does not return - the kernel ends the process. Only a
        // thread with no process (every in-kernel thread) gets the EPERM back,
        // which is the honest answer for something that has no process to end.
        bk_syscall!(ExitGroup, status) as c_int
    }

    unsafe fn fork() -> Result<c_int> {
        // The kernel reads the parent's trap frame itself, so no argument is
        // passed: in the parent the return is the child pid, in the child it is
        // zero, and on failure it is a negative errno. `to_result` turns the
        // last case into `Err`, leaving the parent/child distinction intact.
        to_result(bk_syscall!(Fork) as usize).map(|r| r as c_int)
    }

    unsafe fn execve(
        path: *const c_char,
        argv: *const *const c_char,
        envp: *const *const c_char,
    ) -> Result<c_int> {
        // On success the kernel redirects the return into the new program, so
        // this does not come back either; on failure it is a negative errno
        // (e.g. ENOENT for a missing image).
        to_result(bk_syscall!(Execve, path, argv, envp) as usize).map(|r| r as c_int)
    }

    unsafe fn clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> Result<()> {
        match bk_syscall!(ClockGetTime, clk_id, tp) {
            0 => Ok(()),
            _ => Err(Errno(-1)),
        }
    }
    fn write(fildes: c_int, buf: &[u8]) -> Result<usize> {
        to_result(bk_syscall!(Write, fildes, buf.as_ptr(), buf.len()) as usize)
    }
    unsafe fn clock_getres(_clk_id: clockid_t, _tp: *mut timespec) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    unsafe fn clock_settime(clk_id: clockid_t, tp: *const timespec) -> Result<()> {
        to_result(bk_syscall!(ClockSetTime, clk_id, tp) as usize).map(|_| ())
    }
    unsafe fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> Result<()> {
        if rqtp.is_null() {
            return Err(Errno(-1));
        }
        // blueos is not valid for this syscall now
        match bk_syscall!(ClockNanoSleep, 1, 0, rqtp, rmtp) {
            0 => Ok(()),
            _ => Err(Errno(-1)),
        }
    }
    unsafe fn clock_nanosleep(
        clk_id: clockid_t,
        flags: c_int,
        rqtp: *const timespec,
        rmtp: *mut timespec,
    ) -> Result<()> {
        if rqtp.is_null() {
            return Err(Errno(libc::EINVAL));
        }
        to_result(bk_syscall!(ClockNanoSleep, clk_id, flags, rqtp, rmtp) as usize).map(|_| ())
    }
    fn read(fildes: c_int, buf: &mut [u8]) -> Result<usize> {
        to_result(bk_syscall!(Read, fildes, buf.as_mut_ptr() as *mut c_void, buf.len()) as usize)
    }
    fn access(_path: CStr, _mode: c_int) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn chdir(_path: CStr) -> Result<usize> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Chdir, _path.as_ptr()) as usize)
    }
    fn getcwd(buf: *mut c_char, size: size_t) -> Result<()> {
        to_result(bk_syscall!(Getcwd, buf, size) as usize).map(|_| ())
    }
    fn chmod(_path: CStr, _mode: mode_t) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn fcntl(fildes: c_int, cmd: c_int, arg: usize) -> Result<c_int> {
        to_result(bk_syscall!(Fcntl, fildes, cmd, arg) as usize).map(|e| e as c_int)
    }
    fn getdents(fildes: c_int, buf: &mut [u8]) -> Result<usize> {
        to_result(
            bk_syscall!(GetDents, fildes, buf.as_mut_ptr() as *mut c_void, buf.len()) as usize,
        )
    }
    fn fchmod(_fildes: c_int, _mode: mode_t) -> Result<()> {
        // The kernel has no chmod/fchmod operation. Returning success would
        // claim the mode changed while `stat` keeps reporting the old one.
        Err(Errno(libc::ENOSYS))
    }
    fn fdatasync(_fildes: c_int) -> Result<()> {
        // The filesystem has no delayed write-back: data is visible to every
        // reader as soon as `write` returns, so there is nothing to flush.
        Ok(())
    }
    unsafe fn fstat(_fildes: c_int, _buf: *mut c_char) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(FStat, _fildes, _buf) as usize).map(|_| ())
    }
    unsafe fn fstatvfs(fildes: c_int, buf: *mut statvfs) -> Result<()> {
        // The kernel speaks `struct statfs` (the Linux layout: f_type,
        // f_namelen, f_flags, ...). POSIX `fstatvfs` takes `struct statvfs`,
        // which has no f_type and calls the same fields f_namemax / f_flag and
        // adds f_favail. Handing the caller's buffer to the kernel would
        // therefore write 112 bytes into an 80-byte object and leave every
        // field at the wrong offset, so the call lands in a buffer of ours and
        // the translation happens afterwards. While a process is current that
        // buffer is a user address and the kernel's uptr layer copies through
        // a bounce buffer exactly as it does for a caller-owned one.
        if buf.is_null() {
            return Err(Errno(libc::EFAULT));
        }
        let mut raw = core::mem::MaybeUninit::<libc::statfs>::zeroed();
        to_result(bk_syscall!(FStatfs, fildes, raw.as_mut_ptr()) as usize)?;
        // SAFETY: the syscall succeeded, which means the kernel filled the
        // whole struct before returning 0.
        buf.write(crate::stat::statvfs_from_statfs(&raw.assume_init()));
        Ok(())
    }
    fn link(path1: CStr, path2: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Link, path1.as_ptr(), path2.as_ptr()) as usize).map(|_| ())
    }
    fn fsync(_fildes: c_int) -> Result<()> {
        // Same reason as `fdatasync`: the VFS keeps no dirty state that a
        // later `fsync` could push out.
        Ok(())
    }
    fn ftruncate(_fildes: c_int, _length: off_t) -> Result<()> {
        to_result(bk_syscall!(Ftruncate, _fildes, _length) as usize).map(|_| ())
    }
    fn dup(fildes: c_int) -> Result<c_int> {
        // `dup()` is `fcntl(fildes, F_DUPFD, 0)`: the kernel implements
        // descriptor duplication behind `F_DUPFD`, and its `File::dup`
        // shares the open file description (offset included), so routing
        // here gives POSIX semantics instead of a hard-coded failure.
        const F_DUPFD: c_int = 0;
        to_result(bk_syscall!(Fcntl, fildes, F_DUPFD, 0usize) as usize).map(|e| e as c_int)
    }
    unsafe fn uname(utsname_p: *mut utsname) -> Result<()> {
        // There is no `uname` syscall: the identity is fixed at build time,
        // so fill the caller's `struct utsname` directly instead of returning
        // an all-zero struct (which is not a valid POSIX answer).
        if utsname_p.is_null() {
            return Err(Errno(libc::EFAULT));
        }
        const SYSNAME: &str = "BlueOS";
        const NODENAME: &str = "blueos";
        const RELEASE: &str = "1.0.0";
        const VERSION: &str = "BlueOS 1.0.0";
        const MACHINE: &str = if cfg!(target_arch = "riscv64") {
            "riscv64"
        } else if cfg!(target_arch = "aarch64") {
            "aarch64"
        } else {
            "unknown"
        };

        let u = &mut *utsname_p;
        fill_utsname(&mut u.sysname, SYSNAME);
        fill_utsname(&mut u.nodename, NODENAME);
        fill_utsname(&mut u.release, RELEASE);
        fill_utsname(&mut u.version, VERSION);
        fill_utsname(&mut u.machine, MACHINE);
        fill_utsname(&mut u.domainname, "");
        Ok(())
    }
    fn open(path: CStr, oflag: c_int, mode: mode_t) -> c_int {
        // blueos is not valid for this syscall now
        bk_syscall!(Open, path.as_ptr(), oflag, mode) as c_int
    }

    fn close(fildes: c_int) -> Result<()> {
        to_result(bk_syscall!(Close, fildes) as usize).map(|_| ())
    }
    unsafe fn statfs(_path: CStr, _buf: *mut c_char) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Statfs, _path.as_ptr(), _buf) as usize).map(|_| ())
    }
    fn mkdir(_path: CStr, _mode: mode_t) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Mkdir, _path.as_ptr(), _mode) as usize).map(|_| ())
    }
    fn mkfifo(_path: CStr, _mode: mode_t) -> Result<()> {
        // No FIFO inode kind and no pipe implementation in the kernel yet.
        Err(Errno(libc::ENOSYS))
    }
    fn rmdir(path: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Rmdir, path.as_ptr()) as usize).map(|_| ())
    }
    fn mknod(_path: CStr, _mode: mode_t, _dev: dev_t) -> Result<()> {
        // Device nodes are created by the board at boot; the kernel exposes no
        // syscall that would let a process add one.
        Err(Errno(libc::ENOSYS))
    }
    fn mknodat(_dir_fildes: c_int, _path: CStr, _mode: mode_t, _dev: dev_t) -> Result<()> {
        Err(Errno(libc::ENOSYS))
    }
    fn pause() -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn nice(_inc: c_int) -> Result<c_int> {
        // blueos is not valid for this syscall now
        Ok(0)
    }
    fn readlink(_path: CStr, _buf: &mut [u8]) -> Result<usize> {
        // No symlink inode kind: returning 0 would tell the caller the path
        // is simply not a link, which is a different answer from "unsupported".
        Err(Errno(libc::ENOSYS))
    }
    fn lseek(fildes: c_int, offset: off_t, whence: c_int) -> off_t {
        // blueos is not valid for this syscall now
        bk_syscall!(Lseek, fildes, offset as usize, whence) as off_t
    }
    fn rename(oldpath: CStr, newpath: CStr) -> Result<()> {
        to_result(bk_syscall!(Rename, oldpath.as_ptr(), newpath.as_ptr()) as usize).map(|_| ())
    }
    fn unlink(_path: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Unlink, _path.as_ptr()) as usize).map(|_| ())
    }
    fn symlink(_path1: CStr, _path2: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn sync() -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn umask(mask: mode_t) -> mode_t {
        // blueos is not valid for this syscall now
        mask
    }
    unsafe fn mq_open(
        name: *const c_char,
        oflag: c_int,
        mode: mode_t,
        attr: *const mq_attr,
    ) -> Result<c_int> {
        to_result(bk_syscall!(MqOpen, name, oflag, mode, attr) as usize).map(|fd| fd as c_int)
    }
    unsafe fn mq_close(mqdes: c_int) -> Result<()> {
        to_result(bk_syscall!(MqClose, mqdes) as usize).map(|_| ())
    }
    unsafe fn mq_getsetattr(mqdes: c_int, new: *mut mq_attr, old: *mut mq_attr) -> Result<()> {
        to_result(bk_syscall!(MqGetSetAttr, mqdes, new, old) as usize).map(|_| ())
    }
    unsafe fn mq_unlink(name: *const c_char) -> Result<()> {
        to_result(bk_syscall!(MqUnlink, name) as usize).map(|_| ())
    }
    unsafe fn mq_timedsend(
        mqdes: c_int,
        msg_ptr: *const c_char,
        msg_len: size_t,
        msg_prio: c_uint,
        timeout: *const timespec,
    ) -> Result<c_int> {
        to_result(bk_syscall!(MqTimedSend, mqdes, msg_ptr, msg_len, msg_prio, timeout) as usize)
            .map(|sent| sent as c_int)
    }
    unsafe fn mq_timedreceive(
        mqdes: c_int,
        msg_ptr: *mut c_char,
        msg_len: size_t,
        msg_prio: *mut c_uint,
        timeout: *const timespec,
    ) -> Result<ssize_t> {
        to_result(bk_syscall!(MqTimedReceive, mqdes, msg_ptr, msg_len, msg_prio, timeout) as usize)
            .map(|len| len as ssize_t)
    }
    fn sched_yield() -> Result<()> {
        to_result(bk_syscall!(SchedYield) as usize).map(|_| ())
    }
    unsafe fn sched_rr_get_interval(_pid: c_int, _interval: *mut timespec) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn sched_get_priority_min(_policy: c_int) -> c_int {
        // blueos is not valid for this syscall now
        0
    }
    fn sched_get_priority_max(_policy: c_int) -> c_int {
        // blueos is not valid for this syscall now
        0
    }
    fn pipe2(fds: &mut [c_int], flags: c_int) -> Result<()> {
        if fds.len() < 2 {
            return Err(Errno(libc::EINVAL));
        }
        // The kernel's pipe call carries the same flag set `pipe2` defines.
        // Passing them at creation is the only correct moment: applying
        // `O_CLOEXEC`/`O_NONBLOCK` afterwards with `fcntl` would open a window
        // in which another thread could exec or use the descriptors.
        if flags & !(libc::O_CLOEXEC | libc::O_NONBLOCK) != 0 {
            return Err(Errno(libc::EINVAL));
        }
        to_result(unsafe { bk_syscall!(Pipe, fds.as_mut_ptr(), flags) } as usize).map(|_| ())
    }
    fn pread(_fildes: c_int, _buf: &mut [u8], _off: off_t) -> Result<usize> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }
    fn pwrite(_fildes: c_int, _buf: &[u8], _off: off_t) -> Result<usize> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }

    unsafe fn socket(domain: c_int, type_: c_int, protocol: c_int) -> Result<c_int> {
        to_result(bk_syscall!(Socket, domain, type_, protocol) as usize).map(|fd| fd as c_int)
    }

    unsafe fn bind(socket: c_int, address: *const sockaddr, address_len: socklen_t) -> Result<()> {
        to_result(bk_syscall!(Bind, socket, address, address_len) as usize).map(|_| ())
    }

    unsafe fn connect(
        socket: c_int,
        address: *const sockaddr,
        address_len: socklen_t,
    ) -> Result<()> {
        to_result(bk_syscall!(Connect, socket, address, address_len) as usize).map(|_| ())
    }

    fn listen(socket: c_int, backlog: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(Listen, socket, backlog) } as usize).map(|_| ())
    }

    unsafe fn accept(
        socket: c_int,
        address: *mut sockaddr,
        address_len: *mut socklen_t,
    ) -> Result<c_int> {
        to_result(bk_syscall!(Accept, socket, address, address_len) as usize).map(|fd| fd as c_int)
    }

    fn send(socket: c_int, buffer: &[u8], flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(
            Send,
            socket,
            buffer.as_ptr() as *const core::ffi::c_void,
            buffer.len(),
            flags
        ) as usize)
    }

    unsafe fn sendto(
        socket: c_int,
        buffer: &[u8],
        flags: c_int,
        dest_addr: *const sockaddr,
        dest_len: socklen_t,
    ) -> Result<usize> {
        to_result(bk_syscall!(
            Sendto,
            socket,
            buffer.as_ptr() as *const core::ffi::c_void,
            buffer.len(),
            flags,
            dest_addr,
            dest_len
        ) as usize)
    }

    fn recv(socket: c_int, buffer: &mut [u8], flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(
            Recv,
            socket,
            buffer.as_mut_ptr() as *mut core::ffi::c_void,
            buffer.len(),
            flags
        ) as usize)
    }

    unsafe fn recvfrom(
        socket: c_int,
        buffer: &mut [u8],
        flags: c_int,
        src_addr: *mut sockaddr,
        src_len: *mut socklen_t,
    ) -> Result<usize> {
        to_result(bk_syscall!(
            Recvfrom,
            socket,
            buffer.as_mut_ptr() as *mut core::ffi::c_void,
            buffer.len(),
            flags,
            src_addr,
            src_len
        ) as usize)
    }

    fn shutdown(socket: c_int, how: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(Shutdown, socket, how) } as usize).map(|_| ())
    }

    unsafe fn setsockopt(
        socket: c_int,
        level: c_int,
        option_name: c_int,
        option_value: *const c_void,
        option_len: socklen_t,
    ) -> Result<()> {
        to_result(bk_syscall!(
            Setsockopt,
            socket,
            level,
            option_name,
            option_value as *const core::ffi::c_void,
            option_len
        ) as usize)
        .map(|_| ())
    }

    unsafe fn getsockopt(
        socket: c_int,
        level: c_int,
        option_name: c_int,
        option_value: *mut c_void,
        option_len: *mut socklen_t,
    ) -> Result<()> {
        to_result(bk_syscall!(
            Getsockopt,
            socket,
            level,
            option_name,
            option_value as *mut core::ffi::c_void,
            option_len
        ) as usize)
        .map(|_| ())
    }

    unsafe fn sendmsg(socket: c_int, message: *const msghdr, flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(Sendmsg, socket, message, flags) as usize)
    }

    unsafe fn recvmsg(socket: c_int, message: *mut msghdr, flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(Recvmsg, socket, message, flags) as usize)
    }

    unsafe fn getaddrinfo(
        node: *const c_char,
        service: *const c_char,
        hints: *const libc::addrinfo,
        res: *mut *mut libc::addrinfo,
    ) -> Result<c_int> {
        Ok(bk_syscall!(GetAddrinfo, node, service, hints, res) as c_int)
    }

    unsafe fn freeaddrinfo(res: *mut libc::addrinfo) -> Result<()> {
        bk_syscall!(FreeAddrinfo, res);
        Ok(())
    }

    unsafe fn ioctl(fd: c_int, request: c_ulong, arg: *mut c_void) -> Result<c_int> {
        to_result(bk_syscall!(Ioctl, fd, request, arg as *mut core::ffi::c_void) as usize)
            .map(|r| r as c_int)
    }
}
