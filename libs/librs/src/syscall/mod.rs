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

use crate::{c_str::CStr, errno::Result, mqueue::mq_attr};
use libc::{
    addrinfo, c_char, c_int, c_uint, c_void, clockid_t, dev_t, mode_t, msghdr, off_t, size_t,
    sockaddr, socklen_t, ssize_t, statvfs, timespec, utsname,
};

pub trait Syscall {
    unsafe fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fildes: c_int,
        off: off_t,
    ) -> Result<*mut c_void>;
    unsafe fn munmap(addr: *mut c_void, len: usize) -> Result<()>;
    unsafe fn clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> Result<()>;
    unsafe fn clock_settime(clk_id: clockid_t, tp: *const timespec) -> Result<()>;
    unsafe fn clock_getres(clk_id: clockid_t, tp: *mut timespec) -> Result<()>;
    unsafe fn nanosleep(rqtp: *const timespec, rmtp: *mut timespec) -> Result<()>;
    unsafe fn clock_nanosleep(
        clk_id: clockid_t,
        flags: c_int,
        rqtp: *const timespec,
        rmtp: *mut timespec,
    ) -> Result<()>;
    fn open(path: CStr, oflag: c_int, mode: mode_t) -> c_int;
    fn write(fildes: c_int, buf: &[u8]) -> Result<usize>;
    fn close(fildes: c_int) -> Result<()>;
    fn read(fildes: c_int, buf: &mut [u8]) -> Result<usize>;
    fn access(path: CStr, mode: c_int) -> Result<()>;
    fn chdir(path: CStr) -> Result<usize>;
    fn getcwd(buf: *mut c_char, size: size_t) -> Result<()>;
    fn fcntl(fildes: c_int, cmd: c_int, arg: usize) -> Result<c_int>;
    fn chmod(path: CStr, mode: mode_t) -> Result<()>;
    fn rmdir(path: CStr) -> Result<()>;
    fn fchmod(fildes: c_int, mode: mode_t) -> Result<()>;
    fn getdents(fildes: c_int, buf: &mut [u8]) -> Result<usize>;
    fn fdatasync(fildes: c_int) -> Result<()>;
    unsafe fn fstat(fildes: c_int, buf: *mut c_char) -> Result<()>;
    unsafe fn statfs(path: CStr, buf: *mut c_char) -> Result<()>;
    unsafe fn fstatvfs(fildes: c_int, buf: *mut statvfs) -> Result<()>;
    fn fsync(fildes: c_int) -> Result<()>;
    fn ftruncate(fildes: c_int, length: off_t) -> Result<()>;
    fn dup(fildes: c_int) -> Result<c_int>;
    unsafe fn uname(utsname: *mut utsname) -> Result<()>;
    fn link(path1: CStr, path2: CStr) -> Result<()>;
    fn mkdir(path: CStr, mode: mode_t) -> Result<()>;
    fn mkfifo(path: CStr, mode: mode_t) -> Result<()>;
    fn mknod(path: CStr, mode: mode_t, dev: dev_t) -> Result<()>;
    fn mknodat(dir_fildes: c_int, path: CStr, mode: mode_t, dev: dev_t) -> Result<()>;
    fn pause() -> Result<()>;
    fn nice(inc: c_int) -> Result<c_int>;
    fn readlink(path: CStr, buf: &mut [u8]) -> Result<usize>;
    fn lseek(fildes: c_int, offset: off_t, whence: c_int) -> off_t;
    fn rename(oldpath: CStr, newpath: CStr) -> Result<()>;
    fn umask(mask: mode_t) -> mode_t;
    fn unlink(path: CStr) -> Result<()>;
    fn symlink(path1: CStr, path2: CStr) -> Result<()>;
    fn sync() -> Result<()>;
    unsafe fn mq_open(
        name: *const c_char,
        oflag: c_int,
        mode: mode_t,
        attr: *const mq_attr,
    ) -> Result<c_int>;
    unsafe fn mq_getsetattr(mqdes: c_int, new: *mut mq_attr, old: *mut mq_attr) -> Result<()>;
    unsafe fn mq_unlink(name: *const c_char) -> Result<()>;
    unsafe fn mq_timedsend(
        mqdes: c_int,
        msg_ptr: *const c_char,
        msg_len: size_t,
        msg_prio: c_uint,
        timeout: *const timespec,
    ) -> Result<c_int>;
    unsafe fn mq_timedreceive(
        mqdes: c_int,
        msg_ptr: *mut c_char,
        msg_len: size_t,
        msg_prio: *mut c_uint,
        timeout: *const timespec,
    ) -> Result<ssize_t>;
    unsafe fn sched_rr_get_interval(pid: c_int, interval: *mut timespec) -> Result<()>;
    fn sched_get_priority_min(policy: c_int) -> c_int;
    fn sched_get_priority_max(policy: c_int) -> c_int;
    fn sched_yield() -> Result<()>;
    fn pipe2(fds: &mut [c_int], flags: c_int) -> Result<()>;
    fn pread(fildes: c_int, buf: &mut [u8], off: off_t) -> Result<usize>;
    fn pwrite(fildes: c_int, buf: &[u8], off: off_t) -> Result<usize>;
    unsafe fn socket(domain: c_int, type_: c_int, protocol: c_int) -> Result<c_int>;
    unsafe fn bind(socket: c_int, address: *const sockaddr, address_len: socklen_t) -> Result<()>;
    unsafe fn connect(
        socket: c_int,
        address: *const sockaddr,
        address_len: socklen_t,
    ) -> Result<()>;
    fn listen(socket: c_int, backlog: c_int) -> Result<()>;
    unsafe fn accept(
        socket: c_int,
        address: *mut sockaddr,
        address_len: *mut socklen_t,
    ) -> Result<c_int>;
    fn send(socket: c_int, buffer: &[u8], flags: c_int) -> Result<usize>;
    unsafe fn sendto(
        socket: c_int,
        buffer: &[u8],
        flags: c_int,
        dest_addr: *const sockaddr,
        dest_len: socklen_t,
    ) -> Result<usize>;
    fn recv(socket: c_int, buffer: &mut [u8], flags: c_int) -> Result<usize>;
    unsafe fn recvfrom(
        socket: c_int,
        buffer: &mut [u8],
        flags: c_int,
        src_addr: *mut sockaddr,
        src_len: *mut socklen_t,
    ) -> Result<usize>;
    fn shutdown(socket: c_int, how: c_int) -> Result<()>;
    unsafe fn setsockopt(
        socket: c_int,
        level: c_int,
        option_name: c_int,
        option_value: *const c_void,
        option_len: socklen_t,
    ) -> Result<()>;
    unsafe fn getsockopt(
        socket: c_int,
        level: c_int,
        option_name: c_int,
        option_value: *mut c_void,
        option_len: *mut socklen_t,
    ) -> Result<()>;
    unsafe fn sendmsg(socket: c_int, message: *const msghdr, flags: c_int) -> Result<usize>;
    unsafe fn recvmsg(socket: c_int, message: *mut msghdr, flags: c_int) -> Result<usize>;
    unsafe fn getaddrinfo(
        node: *const c_char,
        service: *const c_char,
        hints: *const addrinfo,
        res: *mut *mut addrinfo,
    ) -> Result<c_int>;
    unsafe fn freeaddrinfo(res: *mut addrinfo) -> Result<()>;
}

pub use self::sys::Sys;

#[cfg(feature = "linux_emulation")]
#[path = "linux_emulation/mod.rs"]
pub mod sys;

#[cfg(not(feature = "linux_emulation"))]
#[path = "blueos/mod.rs"]
pub mod sys;
