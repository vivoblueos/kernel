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

pub use blueos_header::syscalls::NR::{
    Accept, Bind, Connect, Getsockopt, Listen, Recv, Recvfrom, Recvmsg, Send, Sendmsg, Sendto,
    Setsockopt, Shutdown, Socket,
};
use blueos_scal::bk_syscall;
use core::ffi::{c_int, c_size_t, c_ssize_t, c_void};

/// Creates a new communication endpoint
///
/// # C API
/// `int socket(int domain, int type, int protocol);`
///
/// # Returns
/// File descriptor for the new socket or -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/socket.html>
#[no_mangle]
pub extern "C" fn socket(domain: c_int, type_: c_int, protocol: c_int) -> c_int {
    bk_syscall!(Socket, domain, type_, protocol) as c_int
}

/// Bind socket to local address
///
/// # C API
/// `int bind(int socket, const struct sockaddr *address, socklen_t address_len);`
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/bind.html>
#[no_mangle]
pub unsafe extern "C" fn bind(
    socket: c_int,
    address: *const libc::sockaddr,
    address_len: libc::socklen_t,
) -> c_int {
    bk_syscall!(Bind, socket, address, address_len) as c_int
}

/// Connect socket to remote address
///
/// # C API
/// `int connect(int socket, const struct sockaddr *address, socklen_t address_len);`
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/connect.html>
#[no_mangle]
pub unsafe extern "C" fn connect(
    socket: c_int,
    address: *const libc::sockaddr,
    address_len: libc::socklen_t,
) -> c_int {
    bk_syscall!(Connect, socket, address, address_len) as c_int
}

/// Listen for socket connections
///
/// # Note
/// Do not support backlog
///
/// # C API
/// `int listen(int socket, int backlog);`
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/listen.html>
#[no_mangle]
pub extern "C" fn listen(socket: c_int, backlog: c_int) -> c_int {
    bk_syscall!(Listen, socket, backlog) as c_int
}

/// Accept incoming connection
///
/// # C API
/// `int accept(int socket, struct sockaddr *restrict address, socklen_t *restrict address_len);`
///
/// # Returns
/// New socket descriptor or -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/accept.html>
#[no_mangle]
pub unsafe extern "C" fn accept(
    sock_fd: c_int,
    _address: *mut libc::sockaddr,
    _address_len: *mut libc::socklen_t,
) -> c_int {
    bk_syscall!(Accept, sock_fd, _address, _address_len) as c_int
}

/// Send message through socket
///
/// # Support Protocols : TCP
///
/// # C API
/// `ssize_t send(int socket, const void *buffer, size_t length, int flags);`
///
/// # Returns
/// Number of bytes sent or -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/send.html>
#[no_mangle]
pub unsafe extern "C" fn send(
    socket: c_int,
    buffer: *const c_void,
    length: c_size_t,
    flags: c_int,
) -> c_ssize_t {
    bk_syscall!(Send, socket, buffer, length, flags) as c_ssize_t
}

/// Send message through socket
///
/// # Support Protocols : UDP
///
/// # C API
/// `ssize_t sendto(int socket, const void *message, size_t length,
///             int flags, const struct sockaddr *dest_addr,
///             socklen_t dest_len);`
///
/// # Returns
/// Upon successful completion, sendto() shall return the number of bytes sent.
///     Otherwise, -1 shall be returned and errno set to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sendto.html>
#[no_mangle]
pub unsafe extern "C" fn sendto(
    socket: c_int,
    message: *const c_void,
    length: c_size_t,
    flags: c_int,
    dest_addr: *const libc::sockaddr,
    dest_len: libc::socklen_t,
) -> c_ssize_t {
    bk_syscall!(Sendto, socket, message, length, flags, dest_addr, dest_len) as c_ssize_t
}

/// Receive message from socket
///
/// # Support Protocols : ICMP
///
/// # C API
/// `ssize_t recv(int socket, void *buffer, size_t length, int flags);`
///
/// # Returns
/// Number of bytes received or -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/recv.html>
#[no_mangle]
pub unsafe extern "C" fn recv(
    socket: c_int,
    buffer: *mut c_void,
    length: c_size_t,
    flags: c_int,
) -> c_ssize_t {
    bk_syscall!(Recv, socket, buffer, length, flags) as c_ssize_t
}

/// Recv a message from a socket
///
/// # Support Protocols : UDP
///
/// # C API
/// `ssize_t recvfrom(int socket, void *restrict buffer, size_t length,
///     int flags, struct sockaddr *restrict address,
///     socklen_t *restrict address_len);`
///
/// # Returns
/// Upon successful completion, recvfrom() shall return the length of the message in bytes.
///     If no messages are available to be received and the peer has performed an orderly shutdown,
///         recvfrom() shall return 0.
///     Otherwise, the function shall return -1 and set errno to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/recvfrom.html>
#[no_mangle]
pub unsafe extern "C" fn recvfrom(
    socket: c_int,
    buffer: *mut c_void,
    lengeth: c_size_t,
    flags: c_int,
    address: *mut libc::sockaddr,
    address_len: *mut libc::socklen_t,
) -> c_ssize_t {
    bk_syscall!(
        Recvfrom,
        socket,
        buffer,
        lengeth,
        flags,
        address,
        address_len
    ) as c_ssize_t
}

/// Shutdown socket communication
///
/// # C API
/// `int shutdown(int socket, int how);`
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/shutdown.html>
#[no_mangle]
pub extern "C" fn shutdown(socket: c_int, how: c_int) -> c_int {
    bk_syscall!(Shutdown, socket, how) as c_int
}

/// Set the socket options
///
/// # C API
/// `int setsockopt(int socket, int level, int option_name, const void *option_value, socklen_t option_len);`
///
/// # Returns
/// Upon successful completion, setsockopt() shall return 0.
///     Otherwise, -1 shall be returned and errno set to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/setsockopt.html>
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/V2_chap02.html#tag_16_10_16>
#[no_mangle]
pub unsafe extern "C" fn setsockopt(
    socket: c_int,
    level: c_int,
    option_name: c_int,
    option_value: *const c_void,
    option_len: libc::socklen_t,
) -> c_int {
    bk_syscall!(
        Setsockopt,
        socket,
        level,
        option_name,
        option_value,
        option_len
    ) as c_int
}

/// get the socket options
///
/// # C API
/// `int getsockopt(int socket, int level, int option_name, void *restrict option_value, socklen_t *restrict option_len);`
///
/// # Returns
/// Upon successful completion, getsockopt() shall return 0;
///     otherwise, -1 shall be returned and errno set to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/getsockopt.html>
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/V2_chap02.html#tag_16_10_16>
#[no_mangle]
pub unsafe extern "C" fn getsockopt(
    socket: c_int,
    level: c_int,
    option_name: c_int,
    option_value: *mut c_void,
    option_len: *mut libc::socklen_t,
) -> c_int {
    bk_syscall!(
        Getsockopt,
        socket,
        level,
        option_name,
        option_value,
        option_len
    ) as c_int
}

/// Send message through socket
///
/// # Support Protocols : ICMP
///
/// # C API
/// `ssize_t sendmsg(int socket, const struct msghdr *message, int flags)`
///
/// # Returns
/// Upon successful completion, sendmsg() shall return the number of bytes sent.
///     Otherwise, -1 shall be returned and errno set to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/sendmsg.html>
#[no_mangle]
pub unsafe extern "C" fn sendmsg(
    socket: c_int,
    message: *const libc::msghdr,
    flags: c_int,
) -> c_ssize_t {
    bk_syscall!(Sendmsg, socket, message, flags) as c_ssize_t
}

/// Recv message through socket
///
/// # Support Protocols : ICMP
///
/// # C API
/// `ssize_t recvmsg(int socket, struct msghdr *message, int flags);`
///
/// # Returns
/// Upon successful completion, recvmsg() shall return the length of the message in bytes.
///     If no messages are available to be received
///         and the peer has performed an orderly shutdown, recvmsg() shall return 0.
///     Otherwise, -1 shall be returned and errno set to indicate the error.
///
/// # Reference
/// <https://pubs.opengroup.org/onlinepubs/9799919799/functions/recvmsg.html>
#[no_mangle]
pub unsafe extern "C" fn recvmsg(
    socket: c_int,
    message: *mut libc::msghdr,
    flags: c_int,
) -> c_ssize_t {
    bk_syscall!(Recvmsg, socket, message, flags) as c_ssize_t
}
