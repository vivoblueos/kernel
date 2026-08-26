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

//! C API for Socket operations

use crate::{
    error::{self, code},
    net::{
        self, connection::Connection, SocketAddress, SocketDomain, SocketMsghdr, SocketProtocol,
        SocketType, Timeval,
    },
    vfs::{alloc_sock_fd, free_sock_fd, get_sock_by_fd, sock_attach_to_fd},
};
use alloc::{boxed::Box, collections::btree_map::BTreeMap, sync::Arc};
use core::{
    ffi::{c_char, c_int, c_size_t, c_ssize_t, c_void, CStr},
    net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
    str::FromStr,
    sync::atomic::{AtomicI32, Ordering},
    time::Duration,
};
use libc::{size_t, timeval};
use smoltcp::wire::{IpAddress, IpEndpoint};
use spin::rwlock::RwLock;

fn read_socket_option_int(
    option_value: *const c_void,
    option_len: libc::socklen_t,
) -> Option<c_int> {
    if option_value.is_null() || option_len < core::mem::size_of::<c_int>() as libc::socklen_t {
        return None;
    }

    Some(unsafe { core::ptr::read_unaligned(option_value.cast::<c_int>()) })
}

fn write_socket_option_int(
    option_value: *mut c_void,
    option_len: *mut libc::socklen_t,
    value: c_int,
) -> bool {
    if option_value.is_null() || option_len.is_null() {
        return false;
    }

    let actual_len = core::mem::size_of::<c_int>() as libc::socklen_t;
    let provided_len = unsafe { core::ptr::read_unaligned(option_len) };
    if provided_len < actual_len {
        return false;
    }

    unsafe {
        core::ptr::write_unaligned(option_value.cast::<c_int>(), value);
        core::ptr::write_unaligned(option_len, actual_len);
    }
    true
}

fn socket_timeout_from_timeval(timeval: &Timeval) -> Option<Option<Duration>> {
    if timeval.tv_sec < 0 || timeval.tv_usec < 0 || timeval.tv_usec >= 1_000_000 {
        return None;
    }
    if timeval.tv_sec == 0 && timeval.tv_usec == 0 {
        return Some(None);
    }

    Some(Some(Duration::new(
        timeval.tv_sec as u64,
        timeval.tv_usec as u32 * 1_000,
    )))
}

fn write_socket_timeout(
    option_value: *mut c_void,
    option_len: *mut libc::socklen_t,
    timeout: Duration,
) -> bool {
    if option_value.is_null() || option_len.is_null() {
        return false;
    }

    let actual_len = core::mem::size_of::<Timeval>() as libc::socklen_t;
    let provided_len = unsafe { core::ptr::read_unaligned(option_len) };
    if provided_len < actual_len {
        return false;
    }

    unsafe {
        core::ptr::write_unaligned(option_value.cast::<Timeval>(), Timeval::from(timeout));
        core::ptr::write_unaligned(option_len, actual_len);
    }
    true
}

pub fn socket(domain: c_int, type_: c_int, protocol_: c_int) -> c_int {
    let Ok(socket_domain) = SocketDomain::try_from(domain) else {
        // The implementation does not support the specified address family.
        return -libc::EAFNOSUPPORT;
    };

    let Ok(socket_type) = SocketType::try_from(type_) else {
        // The socket type is not supported by the address family, or the socket type is not supported by the implementation.
        return -libc::EPROTOTYPE;
    };

    let Ok(socket_protocol) = SocketProtocol::try_from(protocol_) else {
        // Posix ERRORS : The value of protocol is non-zero and either the protocol is not supported by the address family or the protocol is not supported by the implementation.
        return -libc::EPROTONOSUPPORT;
    };

    let mut flags = 0;
    if (type_ & libc::SO_NONBLOCK) != 0 {
        flags |= libc::O_NONBLOCK;
    }
    if (type_ & libc::SOCK_CLOEXEC) != 0 {
        flags |= libc::O_CLOEXEC;
    }

    let socket = alloc_sock_fd(flags);
    let mut connection = Connection::new(socket, socket_domain, socket_type, socket_protocol);

    connection.set_is_nonblocking((type_ & libc::SO_NONBLOCK) != 0);

    if let Err(e) = connection.create() {
        log::warn!("Failed to create socket: {:?}", e);
        free_sock_fd(socket);
        return -1;
    }
    if let Err(e) = sock_attach_to_fd(socket, Arc::new(connection)) {
        log::error!("sock_attach_to_fd socket fd={} error: {}", socket, e);
        -1
    } else {
        socket
    }
}

pub fn listen(socket: c_int, backlog: c_int) -> c_int {
    log::debug!("fd={}: Listening (backlog={})", socket, backlog);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF;
    };

    if connection.socket_type() == SocketType::SockDgram
        || connection.socket_type() == SocketType::SockRaw
    {
        log::warn!("fd={}: socket protocol does not support listen()", socket);
        return -libc::EOPNOTSUPP;
    }

    if !connection.is_bound() {
        log::warn!("fd={}: socket is unbound", socket);
        return -libc::EDESTADDRREQ;
    }
    connection.listen().map(|_| 0).unwrap_or(-1)
}

pub fn send(socket: c_int, buffer: *const c_void, length: c_size_t, flags: c_int) -> c_ssize_t {
    log::debug!("fd={}: Sending (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    if connection.socket_type() == SocketType::SockDgram
        || connection.socket_type() == SocketType::SockRaw
    {
        log::warn!("fd={}: socket is not connection-mode", socket);
        return -libc::EDESTADDRREQ as c_ssize_t;
    }

    if !connection.is_connected() {
        log::warn!("fd={}: socket is not connected", socket);
        return -libc::ENOTCONN as c_ssize_t;
    }

    if buffer.is_null() || length == 0 {
        return -1;
    }

    let buffer = buffer as *const u8;
    #[allow(unused_mut)]
    let buffer = unsafe { core::slice::from_raw_parts(buffer, length as usize) };

    let f = Box::new(move |send_buffer: &mut [u8]| -> (usize, usize) {
        let send_len = core::cmp::min(send_buffer.len(), length as usize);
        send_buffer[..send_len].copy_from_slice(&buffer[..send_len]);
        log::debug!("[Posix] send closure send_len={}", send_len);
        (send_len, send_len)
    });

    connection
        .send(f, flags)
        .map(|send_sizes| send_sizes.try_into().unwrap_or(-1))
        .unwrap_or(-1)
}

pub fn sendto(
    socket: c_int,
    message: *const c_void,
    length: c_size_t,
    flags: c_int,
    dest_addr: *const libc::sockaddr,
    dest_len: libc::socklen_t,
) -> c_ssize_t {
    log::debug!("fd={}: Sending to (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    if connection.socket_type() == SocketType::SockStream
        || connection.socket_type() == SocketType::SockRaw
    {
        log::warn!("fd={}: socket protocol does not support sendto()", socket);
        return -libc::EOPNOTSUPP as c_ssize_t;
    }

    if message.is_null() || length == 0 {
        return -1;
    }

    let Some(socket_addr) = (unsafe { SocketAddress::from_ptr(dest_addr, dest_len) }) else {
        log::error!("fd={}: Invalid Address", socket);
        return -libc::EBADF as c_ssize_t;
    };

    let Some(remote_endpoint) = socket_addr.create_ip_endpoint() else {
        log::error!("fd={}: Parse endpoint fail", socket);
        return -libc::EADDRNOTAVAIL as c_ssize_t;
    };

    let buf = unsafe { core::slice::from_raw_parts(message as *const u8, length) };

    connection
        .sendto(buf, flags, remote_endpoint)
        .map(|send_sizes| send_sizes.try_into().unwrap_or(-1))
        .unwrap_or(-1)
}

pub fn sendmsg(socket: c_int, message: *const libc::msghdr, flags: c_int) -> c_ssize_t {
    log::debug!("fd={}: sendmsg to (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    // sendmsg only support icmp/icmpv6 now
    if connection.socket_type() == SocketType::SockStream
        || connection.socket_type() == SocketType::SockDgram
        || !(connection.socket_protocol() == SocketProtocol::Icmp
            || connection.socket_protocol() == SocketProtocol::Icmpv6)
    {
        log::warn!("fd={}: socket protocol does not support sendmsg()", socket);
        return -libc::EOPNOTSUPP as c_ssize_t;
    }

    let Some(msghdr) = (unsafe { SocketMsghdr::from_ptr(message) }) else {
        log::error!("Parse Msghdr fail");
        return 0;
    };

    let Some(remote_endpoint) = msghdr.endpoint() else {
        log::error!("Parse endpoint fail");
        return 0;
    };

    // Get packet len
    let packet_len = msghdr.packet_len();

    let identifier = msghdr.parse_icmp_identifier();

    let iov_buffer_ptr = msghdr.msg_iov as usize;
    let iov_buffer_len = msghdr.msg_iovlen;

    // Copy buffer into packet
    let send_payload = Box::new(move |packet: &mut [u8]| -> usize {
        SocketMsghdr::gather_to_buffer(
            iov_buffer_ptr as *const libc::iovec,
            iov_buffer_len as usize,
            packet,
        )
    });

    connection
        .sendmsg(remote_endpoint, identifier, packet_len, send_payload)
        .map(|send_sizes| send_sizes.try_into().unwrap_or(-1))
        .unwrap_or(-1)
}

pub fn recv(socket: c_int, buffer: *mut c_void, length: c_size_t, flags: c_int) -> c_ssize_t {
    log::debug!("fd={}: Receiving (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    if connection.socket_type() == SocketType::SockDgram
        || connection.socket_type() == SocketType::SockRaw
    {
        log::warn!("fd={}: socket is not connection-mode", socket);
        return -libc::EDESTADDRREQ as c_ssize_t;
    }

    if !connection.is_connected() {
        log::warn!(
            "fd={}: A receive is attempted on a connection-mode socket that is not connected",
            socket
        );
        return -libc::ENOTCONN as c_ssize_t;
    }

    if buffer.is_null() || length == 0 {
        return -1;
    }
    let buffer = buffer as *mut u8;
    #[allow(unused_mut)]
    let mut buffer = unsafe { core::slice::from_raw_parts_mut(buffer, length) };

    let f = Box::new(move |recv_buffer: &mut [u8]| -> (usize, usize) {
        let recv_len = core::cmp::min(recv_buffer.len(), length as usize);
        buffer[..recv_len].copy_from_slice(&recv_buffer[..recv_len]);
        log::debug!("[Posix] recv closure recv_len={}", recv_len);
        (recv_len, recv_len)
    });

    connection
        .recv(f)
        .map(|recv_sized| {
            log::debug!("[Posix] recv msg recv_sized={}", recv_sized);
            recv_sized.try_into().unwrap_or(-1)
        })
        .unwrap_or(-1)
}

pub fn recvmsg(socket: c_int, message: *mut libc::msghdr, flags: c_int) -> c_ssize_t {
    log::debug!("fd={}: recvmsg to (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    // recvmsg only support icmp/icmpv6 now
    if connection.socket_type() == SocketType::SockStream
        || connection.socket_type() == SocketType::SockDgram
        || !(connection.socket_protocol() == SocketProtocol::Icmp
            || connection.socket_protocol() == SocketProtocol::Icmpv6)
    {
        log::warn!("fd={}: socket protocol does not support recvmsg()", socket);
        return -libc::EOPNOTSUPP as c_ssize_t;
    }

    let sockaddr_buffer_ptr = message as usize;
    // parse msghdr
    let recv_payload = Box::new(move |payload: &[u8], endpoint: IpEndpoint| -> usize {
        log::debug!("Received packet from {:?}: {:?}", endpoint, payload);

        let Some(msghdr) =
            (unsafe { SocketMsghdr::from_ptr_mut(sockaddr_buffer_ptr as *mut libc::msghdr) })
        else {
            log::error!("Parse Msghdr fail");
            return 0;
        };

        // Write ip address to recv msghdr
        msghdr.fill_ip_endpoint(endpoint);

        // Write payload to recv msghdr
        msghdr.scatter_from_buffer(payload)
    });

    connection
        .recvmsg(recv_payload)
        .map(|recv_sized| recv_sized.try_into().unwrap_or(-1))
        .unwrap_or(-1)
}

pub fn recvfrom(
    socket: c_int,
    buffer: *mut c_void,
    length: c_size_t,
    flags: c_int,
    address: *mut libc::sockaddr,
    address_len: *mut libc::socklen_t,
) -> c_ssize_t {
    log::debug!("fd={}: recvfrom to (flags={})", socket, flags);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF as c_ssize_t;
    };

    if connection.socket_type() == SocketType::SockStream
        || connection.socket_type() == SocketType::SockRaw
    {
        log::warn!("fd={}: socket protocol does not support recvfrom()", socket);
        return -libc::EOPNOTSUPP as c_ssize_t;
    }

    if buffer.is_null() || length == 0 {
        return -1;
    }
    let buffer = buffer as *mut u8;
    #[allow(unused_mut)]
    let mut buffer = unsafe { core::slice::from_raw_parts_mut(buffer, length) };

    let recv_addr = if address.is_null() || address_len.is_null() {
        None
    } else {
        Some((unsafe { &mut *address }, unsafe { &mut *address_len }))
    };

    let recv_payload = Box::new(move |recv_buffer: &[u8], endpoint: IpEndpoint| -> usize {
        log::debug!("Received packet from {:?}", endpoint);

        if let Some((mut address_ref, mut address_len_ref)) = recv_addr {
            net::write_to_sockaddr(
                endpoint,
                address_ref as *mut libc::sockaddr,
                address_len_ref as *mut libc::socklen_t,
            );
        }

        let recv_len = core::cmp::min(recv_buffer.len(), length as usize);
        buffer[..recv_len].copy_from_slice(&recv_buffer[..recv_len]);
        recv_len
    });

    connection
        .recvfrom(recv_payload)
        .map(|recv_sized| recv_sized.try_into().unwrap_or(-1))
        .unwrap_or(-1)
}

pub fn connect(
    socket: c_int,
    address: *const libc::sockaddr,
    address_len: libc::socklen_t,
) -> c_int {
    log::debug!("fd={}: Connecting", socket);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF;
    };

    let Some(socket_addr) = (unsafe { SocketAddress::from_ptr(address, address_len) }) else {
        log::error!("fd={}: Invalid Address", socket);
        return -libc::EBADF;
    };

    let Some(remote_endpoint) = socket_addr.create_ip_endpoint() else {
        log::error!("fd={}: Parse endpoint fail", socket);
        return -libc::EADDRNOTAVAIL;
    };

    connection.connect(remote_endpoint).map(|_| 0).unwrap_or(-1)
}

pub fn bind(socket: c_int, address: *const libc::sockaddr, address_len: libc::socklen_t) -> c_int {
    log::debug!("fd={}: Binding", socket);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF;
    };

    if connection.is_bound() {
        log::warn!("The socket is already bound to an address");
        return -libc::EINVAL;
    }

    let Some(socket_addr) = (unsafe { SocketAddress::from_ptr(address, address_len) }) else {
        log::error!("fd={}: Invalid Address", socket);
        return -libc::EBADF;
    };

    let Some(local_endpoint) = socket_addr.create_ip_endpoint() else {
        log::error!("fd={}: Parse endpoint fail", socket);
        return -libc::EADDRNOTAVAIL;
    };

    connection
        .bind(local_endpoint)
        .map(|_| 0)
        .map_err(|e| log::debug!("bind fail {:#?}", e))
        .unwrap_or(-1)
}

pub fn setsockopt(
    socket: c_int,
    level: c_int,
    option_name: c_int,
    option_value: *const c_void,
    option_len: libc::socklen_t,
) -> c_int {
    log::debug!("fd={}: setsockopt ", socket);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor.", socket);
        return -libc::EBADF;
    };

    if level != libc::SOL_SOCKET {
        // Do not support level other than SOL_SOCKET, like TCP...
        // The option is not supported by the protocol.
        return -libc::ENOPROTOOPT;
    }

    match option_name {
        libc::SO_REUSEADDR => {
            let Some(reuse_address) = read_socket_option_int(option_value, option_len) else {
                return -libc::EINVAL;
            };
            // smoltcp has no address-reuse switch. BlueOS permits one listener per
            // endpoint, but accepts and remembers the POSIX option for compatibility.
            connection.set_reuse_address(reuse_address != 0);
            0
        }
        libc::SO_RCVTIMEO => {
            let Some(timeval) = (unsafe { Timeval::from_ptr(option_value, option_len) }) else {
                return -libc::EINVAL;
            };
            match socket_timeout_from_timeval(timeval) {
                Some(Some(timeout)) => connection.set_recv_timeout(timeout),
                Some(None) => connection.clear_recv_timeout(),
                None => return -libc::EINVAL,
            }
            0
        }
        libc::SO_SNDTIMEO => {
            let Some(timeval) = (unsafe { Timeval::from_ptr(option_value, option_len) }) else {
                return -libc::EINVAL;
            };
            match socket_timeout_from_timeval(timeval) {
                Some(Some(timeout)) => connection.set_send_timeout(timeout),
                Some(None) => connection.clear_send_timeout(),
                None => return -libc::EINVAL,
            }
            0
        }
        // The specified option is invalid at the specified socket level.
        _ => -libc::EINVAL,
    }
}

pub fn getsockopt(
    socket: c_int,
    level: c_int,
    option_name: c_int,
    option_value: *mut c_void,
    option_len: *mut libc::socklen_t,
) -> c_int {
    log::debug!("fd={}: getsockopt ", socket);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor", socket);
        return -libc::EBADF;
    };

    if level != libc::SOL_SOCKET {
        // Do not support level other than SOL_SOCKET, like TCP...
        // The option is not supported by the protocol.
        return -libc::ENOPROTOOPT;
    }

    match option_name {
        libc::SO_REUSEADDR => {
            let value = if connection.reuse_address() { 1 } else { 0 };
            if write_socket_option_int(option_value, option_len, value) {
                0
            } else {
                -libc::EINVAL
            }
        }
        libc::SO_RCVTIMEO => {
            if write_socket_timeout(option_value, option_len, connection.get_recv_timeout()) {
                0
            } else {
                -libc::EINVAL
            }
        }
        libc::SO_SNDTIMEO => {
            if write_socket_timeout(option_value, option_len, connection.get_send_timeout()) {
                0
            } else {
                -libc::EINVAL
            }
        }
        libc::SO_DOMAIN => connection
            .socket_domain()
            .write_to_ptr(option_value, option_len)
            .map(|()| 0)
            .unwrap_or(-1),
        libc::SO_PROTOCOL => connection
            .socket_protocol()
            .into_ptr(option_value, option_len)
            .map(|()| 0)
            .unwrap_or(-1),
        libc::SO_TYPE => connection
            .socket_type()
            .write_to_ptr(option_value, option_len)
            .map(|()| 0)
            .unwrap_or(-1),
        // TODO
        libc::SO_SNDBUF => -1,
        // TODO
        libc::SO_RCVBUF => -1,
        // The specified option is invalid at the specified socket level.
        _ => -libc::EINVAL,
    }
}

pub fn accept(
    socket: c_int,
    _address: *const libc::sockaddr,
    _address_len: libc::socklen_t,
) -> c_int {
    log::debug!("fd={}: Accepting connection", socket);

    if let Err(e) = get_sock_by_fd(socket) {
        log::warn!("fd={}: not a valid file descriptor", socket);
        -libc::EBADF
    } else {
        // return socket fd when exit, do not support backlog
        socket
    }
}

pub fn shutdown(socket: c_int, how: c_int) -> c_int {
    log::debug!("fd={}: Shutting down (how={})", socket, how);

    let Ok(connection) = get_sock_by_fd(socket) else {
        log::error!("fd={}: not a valid file descriptor", socket);
        return -libc::EBADF;
    };
    free_sock_fd(socket);
    connection.shutdown().map(|_| 0).unwrap_or(-1)
}

pub fn getaddrinfo(
    node: *const libc::c_char,
    service: *const libc::c_char,
    hints: *const libc::addrinfo,
    res: *mut *mut libc::addrinfo,
) -> c_int {
    log::debug!("sys_getaddrinfo");
    // TODO
    0
}

pub fn freeaddrinfo(res: *mut libc::addrinfo) -> usize {
    log::debug!("sys_freeaddrinfo");
    // TODO
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn socket_timeout_converts_microseconds() {
        let timeout = socket_timeout_from_timeval(&Timeval {
            tv_sec: 1,
            tv_usec: 500_000,
        });

        assert_eq!(timeout, Some(Some(Duration::from_millis(1_500))));
    }

    #[test]
    fn zero_socket_timeout_clears_the_option() {
        let timeout = socket_timeout_from_timeval(&Timeval {
            tv_sec: 0,
            tv_usec: 0,
        });

        assert_eq!(timeout, Some(None));
    }

    #[test]
    fn socket_timeout_rejects_invalid_values() {
        assert_eq!(
            socket_timeout_from_timeval(&Timeval {
                tv_sec: -1,
                tv_usec: 0,
            }),
            None
        );
        assert_eq!(
            socket_timeout_from_timeval(&Timeval {
                tv_sec: 0,
                tv_usec: 1_000_000,
            }),
            None
        );
    }

    #[test]
    fn socket_option_int_helpers_support_unaligned_buffers() {
        let mut storage = [0u8; core::mem::size_of::<c_int>() + 1];
        let value_ptr = unsafe { storage.as_mut_ptr().add(1) };
        let mut option_len = core::mem::size_of::<c_int>() as libc::socklen_t;

        assert!(write_socket_option_int(
            value_ptr.cast(),
            &mut option_len,
            1
        ));
        assert_eq!(
            read_socket_option_int(value_ptr.cast(), option_len),
            Some(1)
        );
    }
}
