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

pub use self::consts::*;
use super::Syscall;
use crate::{
    c_str::CStr,
    errno::{Errno, Result, SysCallFailed},
    mqueue::mq_attr,
};
use blueos_scal::bk_syscall;
use libc::{
    c_char, c_int, c_uint, c_void, clockid_t, dev_t, mode_t, msghdr, off_t, size_t, sockaddr,
    socklen_t, ssize_t, statvfs, timespec, utsname, EINVAL, S_IFIFO,
};
pub mod consts;

const AT_FDCWD: c_int = -100;
pub const AT_EMPTY_PATH: c_int = 0x1000;

const ERRNO_MAX: usize = 4095;
// convert value returned by syscall to user Result.
pub fn to_result(result: usize) -> Result<usize> {
    if result > ERRNO_MAX.wrapping_neg() {
        Err(Errno(result.wrapping_neg() as _))
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
        Ok(to_result(bk_syscall!(SYS_MMAP, addr, len, prot, flags, fildes, off))? as *mut c_void)
    }

    unsafe fn munmap(addr: *mut c_void, len: usize) -> Result<()> {
        to_result(bk_syscall!(SYS_MUNMAP, addr, len)).map(|_| ())
    }

    unsafe fn clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> Result<()> {
        to_result(bk_syscall!(CLOCK_GETTIME, clk_id, tp)).map(|_| ())
    }
    fn write(fildes: c_int, buf: &[u8]) -> Result<usize> {
        to_result(bk_syscall!(SYS_WRITE, fildes, buf.as_ptr(), buf.len()))
    }
    unsafe fn clock_getres(clk_id: clockid_t, tp: *mut timespec) -> Result<()> {
        to_result(bk_syscall!(CLOCK_GETRES, clk_id, tp)).map(|_| ())
    }
    unsafe fn clock_settime(clk_id: clockid_t, tp: *const timespec) -> Result<()> {
        to_result(bk_syscall!(CLOCK_SETTIME, clk_id, tp)).map(|_| ())
    }
    unsafe fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> Result<()> {
        to_result(bk_syscall!(NANOSLEEP, rqtp, rmtp)).map(|_| ())
    }
    unsafe fn clock_nanosleep(
        clk_id: clockid_t,
        flags: c_int,
        rqtp: *const timespec,
        rmtp: *mut timespec,
    ) -> Result<()> {
        to_result(bk_syscall!(CLOCK_NANOSLEEP, clk_id, flags, rqtp, rmtp)).map(|_| ())
    }
    fn read(fildes: c_int, buf: &mut [u8]) -> Result<usize> {
        to_result(unsafe { bk_syscall!(SYS_READ, fildes, buf.as_mut_ptr(), buf.len()) })
    }
    fn access(path: CStr, mode: c_int) -> Result<()> {
        to_result(bk_syscall!(SYS_ACCESS, path.as_ptr(), mode)).map(|_| ())
    }
    fn chdir(path: CStr) -> Result<usize> {
        to_result(unsafe { bk_syscall!(SYS_CHDIR, path.as_ptr()) })
    }
    fn getcwd(buf: *mut c_char, size: size_t) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_GETCWD, buf, size) }).map(|_| ())
    }
    fn getdents(fildes: c_int, buf: &mut [u8]) -> Result<usize> {
        to_result(unsafe { bk_syscall!(SYS_GETDENTS, fildes, buf.as_mut_ptr(), buf.len()) })
    }
    fn chmod(path: CStr, mode: mode_t) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_CHMOD, path.as_ptr(), mode) }).map(|_| ())
    }
    fn fchmod(fildes: c_int, mode: mode_t) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_FCHMOD, fildes, mode) }).map(|_| ())
    }
    fn fdatasync(fildes: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_FDATASYNC, fildes) }).map(|_| ())
    }
    unsafe fn fstat(fildes: c_int, buf: *mut c_char) -> Result<()> {
        let empty = b"\0";
        let empty_ptr = empty.as_ptr() as *const c_char;
        to_result(unsafe { bk_syscall!(SYS_NEWFSTATAT, fildes, empty_ptr, buf, AT_EMPTY_PATH) })
            .map(|_| ())
    }
    unsafe fn fstatvfs(fildes: c_int, buf: *mut statvfs) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_FSTATFS, fildes, buf) }).map(|_| ())
    }

    fn fsync(fildes: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_FSYNC, fildes) }).map(|_| ())
    }

    fn ftruncate(fildes: c_int, length: off_t) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_FTRUNCATE, fildes, length) }).map(|_| ())
    }

    fn dup(fildes: c_int) -> Result<c_int> {
        to_result(unsafe { bk_syscall!(SYS_DUP, fildes) }).map(|f| f as c_int)
    }

    unsafe fn uname(utsname: *mut utsname) -> Result<()> {
        to_result(bk_syscall!(SYS_UNAME, utsname, 0)).map(|_| ())
    }
    fn open(path: CStr, oflag: c_int, mode: mode_t) -> c_int {
        unsafe { bk_syscall!(SYS_OPEN, path.as_ptr(), oflag, mode) as c_int }
    }
    fn fcntl(fildes: c_int, cmd: c_int, arg: usize) -> Result<c_int> {
        to_result(bk_syscall!(SYS_FCNTL, fildes, cmd, arg)).map(|e| e as c_int)
    }
    fn rmdir(path: CStr) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_RMDIR, path.as_ptr()) }).map(|_| ())
    }
    fn close(fildes: c_int) -> Result<()> {
        to_result(bk_syscall!(SYS_CLOSE, fildes)).map(|_| ())
    }
    unsafe fn statfs(path: CStr, buf: *mut c_char) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_STATFS, path.as_ptr(), buf) }).map(|_| ())
    }
    fn link(path1: CStr, path2: CStr) -> Result<()> {
        to_result(unsafe {
            bk_syscall!(
                SYS_LINKAT,
                AT_FDCWD,
                path1.as_ptr(),
                AT_FDCWD,
                path2.as_ptr(),
                0
            )
        })
        .map(|_| ())
    }
    fn mkdir(path: CStr, mode: mode_t) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_MKDIRAT, AT_FDCWD, path.as_ptr(), mode) }).map(|_| ())
    }

    fn mknod(path: CStr, mode: mode_t, dev: dev_t) -> Result<()> {
        Sys::mknodat(AT_FDCWD, path, mode, dev)
    }
    fn mkfifo(path: CStr, mode: mode_t) -> Result<()> {
        Sys::mknod(path, mode | S_IFIFO, 0)
    }

    fn mknodat(fildes: c_int, path: CStr, mode: mode_t, dev: dev_t) -> Result<()> {
        let k_dev: c_uint = dev as c_uint;
        if k_dev as dev_t != dev {
            return Err(Errno(EINVAL));
        }
        to_result(unsafe { bk_syscall!(SYS_MKNODAT, fildes, path.as_ptr(), mode, k_dev) })
            .map(|_| ())
    }
    fn pause() -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_PAUSE) }).map(|_| ())
    }
    fn nice(inc: c_int) -> Result<c_int> {
        to_result(unsafe { bk_syscall!(SYS_NICE, inc) }).map(|n| n as c_int)
    }
    fn readlink(pathname: CStr, out: &mut [u8]) -> Result<usize> {
        to_result(unsafe {
            bk_syscall!(
                SYS_READLINKAT,
                AT_FDCWD,
                pathname.as_ptr(),
                out.as_mut_ptr(),
                out.len()
            )
        })
    }
    fn lseek(fildes: c_int, offset: off_t, whence: c_int) -> off_t {
        unsafe { bk_syscall!(SYS_LSEEK, fildes, offset, whence) as off_t }
    }

    fn rename(old: CStr, new: CStr) -> Result<()> {
        to_result(unsafe {
            bk_syscall!(SYS_RENAMEAT, AT_FDCWD, old.as_ptr(), AT_FDCWD, new.as_ptr())
        })
        .map(|_| ())
    }
    fn unlink(path: CStr) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_UNLINKAT, AT_FDCWD, path.as_ptr(), 0) }).map(|_| ())
    }

    fn symlink(path1: CStr, path2: CStr) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_SYMLINKAT, path1.as_ptr(), AT_FDCWD, path2.as_ptr()) })
            .map(|_| ())
    }
    fn sync() -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_SYNC) }).map(|_| ())
    }
    fn umask(mask: mode_t) -> mode_t {
        // blueos is not valid for this syscall now
        unsafe { bk_syscall!(SYS_UMASK, mask) as mode_t }
    }
    unsafe fn mq_open(
        name: *const c_char,
        oflag: c_int,
        mode: mode_t,
        attr: *const mq_attr,
    ) -> Result<c_int> {
        to_result(unsafe { bk_syscall!(SYS_MQ_OPEN, name, oflag, mode, attr) })
            .map(|fd| fd as c_int)
    }
    unsafe fn mq_getsetattr(mqdes: c_int, new: *mut mq_attr, old: *mut mq_attr) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_MQ_GETSETATTR, mqdes, new, old) }).map(|_| ())
    }
    unsafe fn mq_unlink(name: *const c_char) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_MQ_UNLINK, name) }).map(|_| ())
    }

    unsafe fn mq_timedsend(
        mqdes: c_int,
        msg_ptr: *const c_char,
        msg_len: size_t,
        msg_prio: c_uint,
        timeout: *const timespec,
    ) -> Result<c_int> {
        to_result(unsafe {
            bk_syscall!(SYS_MQ_TIMEDSEND, mqdes, msg_ptr, msg_len, msg_prio, timeout)
        })
        .map(|e| e as c_int)
    }
    unsafe fn mq_timedreceive(
        mqdes: c_int,
        msg_ptr: *mut c_char,
        msg_len: size_t,
        msg_prio: *mut c_uint,
        timeout: *const timespec,
    ) -> Result<ssize_t> {
        to_result(unsafe {
            bk_syscall!(
                SYS_MQ_TIMEDRECEIVE,
                mqdes,
                msg_ptr,
                msg_len,
                msg_prio,
                timeout
            )
        })
        .map(|e| e as ssize_t)
    }
    fn sched_yield() -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_SCHED_YIELD) }).map(|_| ())
    }
    fn sched_get_priority_min(policy: c_int) -> c_int {
        unsafe { bk_syscall!(SYS_SCHED_GET_PRIORITY_MIN, policy) as c_int }
    }
    fn sched_get_priority_max(policy: c_int) -> c_int {
        unsafe { bk_syscall!(SYS_SCHED_GET_PRIORITY_MAX, policy) as c_int }
    }
    unsafe fn sched_rr_get_interval(pid: c_int, interval: *mut timespec) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_SCHED_RR_GET_INTERVAL, pid, interval) }).map(|_| ())
    }
    fn pipe2(fds: &mut [c_int], flags: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_PIPE2, fds.as_ptr(), flags) }).map(|_| ())
    }
    fn pread(fildes: c_int, buf: &mut [u8], off: off_t) -> Result<usize> {
        to_result(unsafe { bk_syscall!(SYS_PREAD, fildes, buf.as_mut_ptr(), buf.len(), off) })
    }
    fn pwrite(fildes: c_int, buf: &[u8], off: off_t) -> Result<usize> {
        to_result(unsafe { bk_syscall!(SYS_PWRITE, fildes, buf.as_ptr(), buf.len(), off) })
    }

    unsafe fn socket(domain: c_int, type_: c_int, protocol: c_int) -> Result<c_int> {
        to_result(bk_syscall!(SYS_SOCKET, domain, type_, protocol)).map(|fd| fd as c_int)
    }

    unsafe fn bind(socket: c_int, address: *const sockaddr, address_len: socklen_t) -> Result<()> {
        to_result(bk_syscall!(SYS_BIND, socket, address, address_len)).map(|_| ())
    }

    unsafe fn connect(
        socket: c_int,
        address: *const sockaddr,
        address_len: socklen_t,
    ) -> Result<()> {
        to_result(bk_syscall!(SYS_CONNECT, socket, address, address_len)).map(|_| ())
    }

    fn listen(socket: c_int, backlog: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_LISTEN, socket, backlog) }).map(|_| ())
    }

    unsafe fn accept(
        socket: c_int,
        address: *mut sockaddr,
        address_len: *mut socklen_t,
    ) -> Result<c_int> {
        to_result(bk_syscall!(SYS_ACCEPT, socket, address, address_len)).map(|fd| fd as c_int)
    }

    fn send(socket: c_int, buffer: &[u8], flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(
            SYS_SEND,
            socket,
            buffer.as_ptr() as *const c_void,
            buffer.len(),
            flags
        ))
    }

    unsafe fn sendto(
        socket: c_int,
        buffer: &[u8],
        flags: c_int,
        dest_addr: *const sockaddr,
        dest_len: socklen_t,
    ) -> Result<usize> {
        to_result(bk_syscall!(
            SYS_SENDTO,
            socket,
            buffer.as_ptr() as *const c_void,
            buffer.len(),
            flags,
            dest_addr,
            dest_len
        ))
    }

    fn recv(socket: c_int, buffer: &mut [u8], flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(
            SYS_RECV,
            socket,
            buffer.as_mut_ptr() as *mut c_void,
            buffer.len(),
            flags
        ))
    }

    unsafe fn recvfrom(
        socket: c_int,
        buffer: &mut [u8],
        flags: c_int,
        src_addr: *mut sockaddr,
        src_len: *mut socklen_t,
    ) -> Result<usize> {
        to_result(bk_syscall!(
            SYS_RECVFROM,
            socket,
            buffer.as_mut_ptr() as *mut c_void,
            buffer.len(),
            flags,
            src_addr,
            src_len
        ))
    }

    fn shutdown(socket: c_int, how: c_int) -> Result<()> {
        to_result(unsafe { bk_syscall!(SYS_SHUTDOWN, socket, how) }).map(|_| ())
    }

    unsafe fn setsockopt(
        socket: c_int,
        level: c_int,
        option_name: c_int,
        option_value: *const c_void,
        option_len: socklen_t,
    ) -> Result<()> {
        to_result(bk_syscall!(
            SYS_SETSOCKOPT,
            socket,
            level,
            option_name,
            option_value,
            option_len
        ))
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
            SYS_GETSOCKOPT,
            socket,
            level,
            option_name,
            option_value,
            option_len
        ))
        .map(|_| ())
    }

    unsafe fn sendmsg(socket: c_int, message: *const msghdr, flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(SYS_SENDMSG, socket, message, flags))
    }

    unsafe fn recvmsg(socket: c_int, message: *mut msghdr, flags: c_int) -> Result<usize> {
        to_result(bk_syscall!(SYS_RECVMSG, socket, message, flags))
    }

    unsafe fn getaddrinfo(
        node: *const c_char,
        service: *const c_char,
        hints: *const libc::addrinfo,
        res: *mut *mut libc::addrinfo,
    ) -> Result<c_int> {
        to_result(bk_syscall!(SYS_GETADDRINFO, node, service, hints, res) as usize)
    }

    unsafe fn freeaddrinfo(res: *mut libc::addrinfo) -> Result<()> {
        to_result(bk_syscall!(SYS_FREEADDRINFO, res))
    }
}
