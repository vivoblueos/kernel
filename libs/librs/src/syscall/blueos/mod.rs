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
    Accept, Bind, Chdir, ClockGetTime, Close, Connect, FStat, Fcntl, FreeAddrinfo, Ftruncate,
    GetAddrinfo, GetDents, Getcwd, Getsockopt, Link, Listen, Lseek, Mkdir, NanoSleep, Open, Read,
    Recv, Recvfrom, Recvmsg, Rmdir, Send, Sendmsg, Sendto, Setsockopt, Shutdown, Socket, Statfs,
    Unlink, Write,
};
use blueos_scal::bk_syscall;
use libc::{
    c_char, c_int, c_uint, c_void, clockid_t, dev_t, mode_t, msghdr, off_t, size_t, sockaddr,
    socklen_t, ssize_t, statvfs, timespec, utsname,
};

// convert value returned by syscall to user Result.
const ERRNO_MAX: usize = 4095;
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
        _addr: *mut c_void,
        _len: usize,
        _prot: c_int,
        _flags: c_int,
        _fildes: c_int,
        _off: off_t,
    ) -> Result<*mut c_void> {
        // This is not valid for blueos now
        Err(Errno(-1))
    }

    unsafe fn munmap(_addr: *mut c_void, _len: usize) -> Result<()> {
        // This is not valid for blueos now, do nothing
        Ok(())
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
    unsafe fn clock_settime(_clk_id: clockid_t, _tp: *const timespec) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    unsafe fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> Result<()> {
        if rqtp.is_null() {
            return Err(Errno(-1));
        }
        // blueos is not valid for this syscall now
        match bk_syscall!(NanoSleep, 1, 0, rqtp, rmtp) {
            0 => Ok(()),
            _ => Err(Errno(-1)),
        }
    }
    unsafe fn clock_nanosleep(
        _clk_id: clockid_t,
        _flags: c_int,
        _rqtp: *const timespec,
        _rmtp: *mut timespec,
    ) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
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
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn fdatasync(_fildes: c_int) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    unsafe fn fstat(_fildes: c_int, _buf: *mut c_char) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(FStat, _fildes, _buf) as usize).map(|_| ())
    }
    unsafe fn fstatvfs(_fildes: c_int, _buf: *mut statvfs) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn link(path1: CStr, path2: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Link, path1.as_ptr(), path2.as_ptr()) as usize).map(|_| ())
    }
    fn fsync(_fildes: c_int) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn ftruncate(_fildes: c_int, _length: off_t) -> Result<()> {
        to_result(bk_syscall!(Ftruncate, _fildes, _length) as usize).map(|_| ())
    }
    fn dup(_fildes: c_int) -> Result<c_int> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }
    unsafe fn uname(_utsname: *mut utsname) -> Result<()> {
        // blueos is not valid for this syscall now
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
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn rmdir(path: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        to_result(bk_syscall!(Rmdir, path.as_ptr()) as usize).map(|_| ())
    }
    fn mknod(_path: CStr, _mode: mode_t, _dev: dev_t) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    fn mknodat(_dir_fildes: c_int, _path: CStr, _mode: mode_t, _dev: dev_t) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
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
        // blueos is not valid for this syscall now
        Ok(0)
    }
    fn lseek(fildes: c_int, offset: off_t, whence: c_int) -> off_t {
        // blueos is not valid for this syscall now
        bk_syscall!(Lseek, fildes, offset as usize, whence) as off_t
    }
    fn rename(_oldpath: CStr, _newpath: CStr) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
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
        _name: *const c_char,
        _oflag: c_int,
        _mode: mode_t,
        _attr: *const mq_attr,
    ) -> Result<c_int> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }
    unsafe fn mq_getsetattr(_mqdes: c_int, _new: *mut mq_attr, _old: *mut mq_attr) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    unsafe fn mq_unlink(_name: *const c_char) -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
    }
    unsafe fn mq_timedsend(
        _mqdes: c_int,
        _msg_ptr: *const c_char,
        _msg_len: size_t,
        _msg_prio: c_uint,
        _timeout: *const timespec,
    ) -> Result<c_int> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }
    unsafe fn mq_timedreceive(
        _mqdes: c_int,
        _msg_ptr: *mut c_char,
        _msg_len: size_t,
        _msg_prio: *mut c_uint,
        _timeout: *const timespec,
    ) -> Result<ssize_t> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
    }
    fn sched_yield() -> Result<()> {
        // blueos is not valid for this syscall now
        Ok(())
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
    fn pipe2(_fds: &mut [c_int], _flags: c_int) -> Result<()> {
        // blueos is not valid for this syscall now
        Err(Errno(-1))
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
}
