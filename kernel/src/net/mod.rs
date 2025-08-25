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

pub(crate) mod connection;
pub(crate) mod connection_err;
pub(crate) mod net_interface;
pub(crate) mod net_manager;
pub(crate) mod port_generator;
pub(crate) mod socket;
pub mod syscalls;

use core::{
    net::{Ipv4Addr, SocketAddr},
    time::Duration,
};

use core::{
    cell::RefCell,
    ffi::{c_int, c_void},
    sync::atomic::AtomicUsize,
};
use smoltcp::wire::{IpAddress, IpEndpoint};

use crate::net::socket::socket_err::SocketError;

pub type SocketFd = i32;
pub type SocketResult = Result<usize, SocketError>;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum SocketDomain {
    AfInet,
    AfInet6,
}

impl TryFrom<c_int> for SocketDomain {
    type Error = SocketError;

    fn try_from(type_c_int: c_int) -> Result<Self, Self::Error> {
        match type_c_int {
            libc::AF_INET => Ok(SocketDomain::AfInet),
            libc::AF_INET6 => Ok(SocketDomain::AfInet6),
            _ => Err(SocketError::UnsupportedSocketDomain(type_c_int as i32)),
        }
    }
}

impl From<SocketDomain> for c_int {
    fn from(socket_domain: SocketDomain) -> c_int {
        match socket_domain {
            SocketDomain::AfInet => libc::AF_INET,
            SocketDomain::AfInet6 => libc::AF_INET6,
        }
    }
}

impl PartialEq<c_int> for SocketDomain {
    fn eq(&self, other: &c_int) -> bool {
        match self {
            SocketDomain::AfInet => libc::AF_INET == *other,
            SocketDomain::AfInet6 => libc::AF_INET6 == *other,
        }
    }
}

impl SocketDomain {
    pub fn write_to_ptr(
        &self,
        option_value: *mut c_void,
        option_len: *mut libc::socklen_t,
    ) -> Result<(), c_int> {
        if option_len.is_null() || option_value.is_null() {
            return Err(-1);
        }

        let user_len = unsafe { *option_len };
        let actual_len = core::mem::size_of::<libc::c_int>() as libc::socklen_t;

        if user_len < actual_len {
            return Err(-1);
        }

        let option_value = option_value as *mut c_int;
        unsafe {
            *option_value = (*self).into();
            *option_len = actual_len;
        };

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, PartialOrd, Ord)]
pub enum SocketType {
    SockStream, // TCP
    SockDgram,  // UDP
    SockRaw,    // ICMPv4/ICMPv6 only
}

impl TryFrom<c_int> for SocketType {
    type Error = SocketError;

    fn try_from(type_c_int: c_int) -> Result<Self, Self::Error> {
        // Parse the low 8 bits, because type may contain the bitwise-inclusive OR of flags
        match type_c_int & 0xFF {
            libc::SOCK_STREAM => Ok(SocketType::SockStream),
            libc::SOCK_DGRAM => Ok(SocketType::SockDgram),
            libc::SOCK_RAW => Ok(SocketType::SockRaw),
            _ => Err(SocketError::UnsupportedSocketType(type_c_int as i32)),
        }
    }
}

impl From<SocketType> for c_int {
    fn from(socket_type: SocketType) -> c_int {
        match socket_type {
            SocketType::SockStream => libc::SOCK_STREAM,
            SocketType::SockDgram => libc::SOCK_DGRAM,
            SocketType::SockRaw => libc::SOCK_RAW,
        }
    }
}

impl SocketType {
    pub fn write_to_ptr(
        &self,
        option_value: *mut c_void,
        option_len: *mut libc::socklen_t,
    ) -> Result<(), c_int> {
        if option_len.is_null() || option_value.is_null() {
            return Err(-1);
        }

        let user_len = unsafe { *option_len };
        let actual_len = core::mem::size_of::<libc::c_int>() as libc::socklen_t;

        if user_len < actual_len {
            return Err(-1);
        }

        let option_value = option_value as *mut c_int;
        unsafe {
            *option_value = (*self).into();
            *option_len = actual_len;
        };

        Ok(())
    }
}

impl core::fmt::Display for SocketType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SocketType::SockStream => write!(f, "SocketType(SockStream)"),
            SocketType::SockDgram => write!(f, "SocketType(SockDgram)"),
            SocketType::SockRaw => write!(f, "SocketType(SockRaw)"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum SocketProtocol {
    Ip,
    Ipv6,
    Icmp,
    Icmpv6,
    Raw,
    Tcp,
    Udp,
}

impl TryFrom<c_int> for SocketProtocol {
    type Error = SocketError;

    fn try_from(type_c_int: c_int) -> Result<Self, Self::Error> {
        let socket_protocol = match type_c_int {
            libc::IPPROTO_IP => SocketProtocol::Ip,
            libc::IPPROTO_IPV6 => SocketProtocol::Ipv6,
            libc::IPPROTO_ICMP => SocketProtocol::Icmp,
            libc::IPPROTO_ICMPV6 => SocketProtocol::Icmpv6,
            libc::IPPROTO_TCP => SocketProtocol::Tcp,
            libc::IPPROTO_UDP => SocketProtocol::Udp,
            _ => return Err(SocketError::UnsupportedSocketProtocol(type_c_int)),
        };
        Ok(socket_protocol)
    }
}

impl From<SocketProtocol> for c_int {
    fn from(socket_protocol: SocketProtocol) -> c_int {
        match socket_protocol {
            SocketProtocol::Ip => libc::IPPROTO_IP,
            SocketProtocol::Ipv6 => libc::IPPROTO_IPV6,
            SocketProtocol::Icmp => libc::IPPROTO_ICMP,
            SocketProtocol::Icmpv6 => libc::IPPROTO_ICMPV6,
            SocketProtocol::Tcp => libc::IPPROTO_TCP,
            SocketProtocol::Udp => libc::IPPROTO_UDP,
            SocketProtocol::Raw => libc::IPPROTO_RAW,
        }
    }
}

impl SocketProtocol {
    pub fn into_ptr(
        &self,
        option_value: *mut c_void,
        option_len: *mut libc::socklen_t,
    ) -> Result<(), c_int> {
        if option_len.is_null() || option_value.is_null() {
            return Err(-1);
        }

        let user_len = unsafe { *option_len };
        let actual_len = core::mem::size_of::<libc::c_int>() as libc::socklen_t;

        if user_len < actual_len {
            return Err(-1);
        }

        let option_value = option_value as *mut c_int;
        unsafe {
            *option_value = (*self).into();
            *option_len = actual_len;
        };

        Ok(())
    }
}

#[repr(C)]
pub struct SocketAddress {
    pub sa_len: u8,
    pub sa_family: libc::sa_family_t,
    pub sa_data: [libc::c_char; 14],
}

#[repr(C)]
pub struct SocketAddressV4 {
    pub sin_len: u8,
    pub sin_family: libc::sa_family_t,
    pub sin_port: libc::in_port_t,
    pub sin_addr: libc::in_addr,
    pub sin_vport: libc::in_port_t,
    pub sin_zero: [u8; 6],
}

#[repr(C)]
pub struct SocketAddressV6 {
    pub sin6_len: u8,
    pub sin6_family: libc::sa_family_t,
    pub sin6_port: libc::in_port_t,
    pub sin6_flowinfo: u32,
    pub sin6_addr: libc::in6_addr,
    pub sin6_vport: libc::in_port_t,
    pub sin6_scope_id: u32,
}

impl SocketAddress {
    pub unsafe fn from_ptr<'a>(
        ptr: *const libc::sockaddr,
        len: libc::socklen_t,
    ) -> Option<&'a Self> {
        if ptr.is_null() || (len as usize) < core::mem::size_of::<libc::sockaddr>() {
            return None;
        }

        Some(&*(ptr as *const Self))
    }

    pub fn create_ip_endpoint(&self) -> Option<IpEndpoint> {
        match self.sa_family as i32 {
            libc::AF_INET => {
                let v4_ptr = self as *const _ as *const SocketAddressV4;
                (unsafe { v4_ptr.as_ref() }).map(|v4_ref| v4_ref.create_ip_endpoint())
            }
            libc::AF_INET6 => {
                let v6_ptr = self as *const _ as *const SocketAddressV6;
                (unsafe { v6_ptr.as_ref() }).map(|v6_ref| v6_ref.create_ip_endpoint())
            }
            _ => None,
        }
    }
}

impl SocketAddressV4 {
    pub unsafe fn from_ptr<'a>(
        ptr: *const libc::sockaddr_in,
        len: libc::socklen_t,
    ) -> Option<&'a Self> {
        if ptr.is_null() || (len as usize) < core::mem::size_of::<libc::sockaddr_in>() {
            return None;
        }

        Some(&*(ptr as *const Self))
    }

    pub fn create_ip_endpoint(&self) -> IpEndpoint {
        IpEndpoint {
            addr: IpAddress::Ipv4(core::net::Ipv4Addr::from(
                self.sin_addr.s_addr.to_ne_bytes(),
            )),
            port: u16::from_be(self.sin_port),
        }
    }
}

impl SocketAddressV6 {
    pub fn create_ip_endpoint(&self) -> IpEndpoint {
        IpEndpoint {
            addr: IpAddress::Ipv6(core::net::Ipv6Addr::from(self.sin6_addr.s6_addr)),
            port: u16::from_be(self.sin6_port),
        }
    }
}

#[repr(C)]
pub struct Timeval {
    pub tv_sec: libc::time_t,
    pub tv_usec: libc::suseconds_t,
}

impl Timeval {
    pub unsafe fn from_ptr<'a>(ptr: *const c_void, len: libc::socklen_t) -> Option<&'a Self> {
        let ptr = ptr as *const libc::timeval;
        if ptr.is_null() || len != (core::mem::size_of::<libc::timeval>() as libc::socklen_t) {
            None
        } else {
            Some(&*(ptr as *const Self))
        }
    }
}

crate::static_assert!(size_of::<Timeval>() == size_of::<libc::timeval>());

impl From<Duration> for Timeval {
    fn from(duration: Duration) -> Timeval {
        let sec = duration.as_secs() as libc::time_t;
        let usec = duration.subsec_micros() as libc::suseconds_t;
        debug_assert!(usec >= 0); // usec >= 0 always holds
        Timeval {
            tv_sec: sec,
            tv_usec: usec,
        }
    }
}

impl From<&Timeval> for Duration {
    fn from(timeval: &Timeval) -> Self {
        Duration::new(timeval.tv_sec as u64, timeval.tv_usec as u32)
    }
}

/// ICMP Message with identifier
const IDENTIFIER_TYPES: [u8; 10] = [
    0, // Echo Request
    8, // Echo Reply
    13, 14, 15, 16,  // Timestamp / Information X Request / Reply (Deprecated)
    42,  // Extend Echo Request : Extend Ping (RFC8335)
    43,  // Extend Echo Reply : Extend Ping (RFC8335)
    128, // ICMPv6 Echo Request
    129, // ICMPv6 Echo Reply
];

#[repr(C)]
pub struct SocketMsghdr {
    pub msg_name: *mut libc::c_void,
    pub msg_namelen: libc::socklen_t,
    pub msg_iov: *mut libc::iovec,
    pub msg_iovlen: libc::size_t,
    pub msg_control: *mut libc::c_void,
    pub msg_controllen: libc::size_t,
    pub msg_flags: libc::c_int,
}

impl core::fmt::Debug for SocketMsghdr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SocketMsghdr")
            .field("msg_name", &self.msg_name)
            .field("msg_namelen", &self.msg_namelen)
            .field("msg_iov", &self.msg_iov)
            .field("msg_iovlen", &self.msg_iovlen)
            .field("msg_control", &self.msg_control)
            .field("msg_controllen", &self.msg_controllen)
            .field("msg_flags", &format_args!("0x{:x}", self.msg_flags))
            .finish()
    }
}

impl SocketMsghdr {
    pub unsafe fn from_ptr<'a>(ptr: *const libc::msghdr) -> Option<&'a Self> {
        if ptr.is_null() {
            None
        } else {
            Some(&*(ptr as *const Self))
        }
    }

    pub unsafe fn from_ptr_mut<'a>(ptr: *mut libc::msghdr) -> Option<&'a mut Self> {
        if ptr.is_null() {
            None
        } else {
            Some(&mut *(ptr as *mut SocketMsghdr))
        }
    }

    pub fn fill_ip_endpoint(&mut self, endpoint: IpEndpoint) {
        write_to_sockaddr(
            endpoint,
            self.msg_name.cast::<libc::sockaddr>(),
            &mut self.msg_namelen as *mut libc::socklen_t,
        );
    }

    pub fn scatter_from_buffer(&mut self, payload: &[u8]) -> usize {
        if payload.is_empty() || self.msg_iov.is_null() || self.msg_iovlen == 0 {
            return 0;
        }

        let mut remaining = payload;
        let mut total_copied = 0;
        for i in 0..(self.msg_iovlen as usize) {
            // get next iov
            let iov = unsafe { &*(self.msg_iov).add(i) };

            if iov.iov_base.is_null() || iov.iov_len == 0 {
                continue;
            }

            // copy into iov
            let buffer_len = iov.iov_len as usize;
            let copy_len = remaining.len().min(buffer_len);

            let dst =
                unsafe { core::slice::from_raw_parts_mut(iov.iov_base.cast::<u8>(), buffer_len) }; // TODO copy_len to buffer_len
            let (dst_part, src_part) = (&mut dst[..copy_len], &remaining[..copy_len]);

            dst_part.copy_from_slice(src_part);

            remaining = &remaining[copy_len..];
            total_copied += copy_len;

            if remaining.is_empty() {
                break;
            }
        }

        total_copied
    }

    pub fn gather_to_buffer(
        msg_iov: *const libc::iovec,
        msg_iovlen: usize,
        buffer: &mut [u8],
    ) -> usize {
        if buffer.is_empty() || msg_iov.is_null() || msg_iovlen == 0 {
            return 0;
        }

        let mut destination = buffer;
        let mut total_copied = 0;
        for i in 0..(msg_iovlen as usize) {
            if destination.is_empty() {
                break;
            }

            let iov = unsafe { &*msg_iov.add(i) };

            if iov.iov_base.is_null() || iov.iov_len == 0 {
                continue;
            }

            let source = unsafe {
                core::slice::from_raw_parts(iov.iov_base.cast::<u8>(), iov.iov_len as usize)
            };
            let copy_len = destination.len().min(source.len());

            destination[..copy_len].copy_from_slice(&source[..copy_len]);

            destination = &mut destination[copy_len..];
            total_copied += copy_len;
        }

        total_copied
    }

    pub fn endpoint(&self) -> Option<IpEndpoint> {
        unsafe { SocketAddress::from_ptr(self.msg_name as *const libc::sockaddr, self.msg_namelen) }
            .and_then(|addr| addr.create_ip_endpoint())
    }

    pub fn packet_len(&self) -> usize {
        unsafe { core::slice::from_raw_parts(self.msg_iov, self.msg_iovlen as usize) }
            .iter()
            .map(|iov| iov.iov_len)
            .sum()
    }

    pub fn parse_icmp_identifier(&self) -> Option<u16> {
        if self.msg_iovlen == 0 {
            return None;
        }

        let first = unsafe { &*self.msg_iov };
        if first.iov_len < 1 {
            return None;
        }

        let icmp_type = unsafe { *(first.iov_base as *const u8) };

        // Check ICMP Message Type
        if !IDENTIFIER_TYPES.contains(&icmp_type) {
            return None;
        }

        let mut offset = 0;
        let mut high_byte = None;

        for i in 0..self.msg_iovlen {
            let vec = unsafe { &*self.msg_iov.add(i) };
            let data = unsafe {
                core::slice::from_raw_parts(vec.iov_base as *const u8, vec.iov_len as usize)
            };

            if data.is_empty() {
                continue;
            }

            let start = 4usize.saturating_sub(offset);
            let end = 6usize.saturating_sub(offset);

            match () {
                _ if start < data.len() && end <= data.len() => {
                    return Some(u16::from_be_bytes([data[start], data[start + 1]]))
                }

                _ if start < data.len() => high_byte = Some(data[start]),

                _ if !data.is_empty() && high_byte.is_some() => {
                    return Some(u16::from_be_bytes([high_byte.take().unwrap(), data[0]]))
                }

                _ => {}
            }

            offset += data.len();
        }

        None
    }
}

pub fn write_to_sockaddr(
    endpoint: IpEndpoint,
    sockaddr_ptr: *mut libc::sockaddr,
    socklen_ptr: *mut libc::socklen_t,
) {
    if socklen_ptr as usize >= core::mem::size_of::<libc::sockaddr>() {
        match endpoint.addr {
            IpAddress::Ipv4(ipv4) => unsafe {
                let addr_len = core::mem::size_of::<libc::sockaddr_in>();
                let sockaddr_ptr = sockaddr_ptr.cast::<libc::sockaddr_in>();
                // addr
                (*sockaddr_ptr).sin_len = addr_len as u8;
                (*sockaddr_ptr).sin_family = libc::AF_INET as libc::sa_family_t;
                (*sockaddr_ptr).sin_port = u16::from_be(endpoint.port);
                (*sockaddr_ptr).sin_addr.s_addr = u32::from_ne_bytes(ipv4.octets());
                let addr_ptr = sockaddr_ptr
                    .cast::<u8>()
                    .add(core::mem::offset_of!(libc::sockaddr_in, sin_zero));
                core::ptr::write_bytes(addr_ptr, 0, 6);

                // addr len
                *socklen_ptr = addr_len as libc::socklen_t;
            },
            IpAddress::Ipv6(ipv6) => unsafe {
                let addr_len = core::mem::size_of::<libc::sockaddr_in6>();
                let sockaddr_ptr = sockaddr_ptr.cast::<libc::sockaddr_in6>();

                // addr
                (*sockaddr_ptr).sin6_len = addr_len as u8;
                (*sockaddr_ptr).sin6_family = libc::AF_INET6 as libc::sa_family_t;
                (*sockaddr_ptr).sin6_port = u16::from_be(endpoint.port);
                (*sockaddr_ptr).sin6_flowinfo = 0;
                (*sockaddr_ptr).sin6_addr.s6_addr = ipv6.octets();
                (*sockaddr_ptr).sin6_vport = 0;
                (*sockaddr_ptr).sin6_scope_id = 0;

                // addr len
                *socklen_ptr = addr_len as libc::socklen_t;
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use core::mem::size_of;

    #[test]
    fn try_from_valid_values() {
        // test valid values
        assert_eq!(
            SocketDomain::try_from(libc::AF_INET).unwrap(),
            SocketDomain::AfInet
        );
        assert_eq!(
            SocketDomain::try_from(libc::AF_INET6).unwrap(),
            SocketDomain::AfInet6
        );
    }

    #[test]
    fn try_from_invalid_value() {
        assert!(matches!(
            SocketDomain::try_from(-1).unwrap_err(),
            SocketError::UnsupportedSocketDomain(-1)
        ));
    }

    #[test]
    fn into_c_int() {
        assert_eq!(libc::AF_INET, SocketDomain::AfInet.into());
        assert_eq!(libc::AF_INET6, SocketDomain::AfInet6.into());
    }

    #[test]
    fn partial_eq_with_c_int() {
        assert!(SocketDomain::AfInet == libc::AF_INET);
        assert!(SocketDomain::AfInet6 == libc::AF_INET6);
        assert!(SocketDomain::AfInet != libc::AF_INET6);
    }

    #[test]
    fn write_to_ptr_success() {
        let domain = SocketDomain::AfInet;
        let mut value: c_int = 0;
        let mut len = size_of::<c_int>() as libc::socklen_t;

        let result = domain.write_to_ptr(
            &mut value as *mut _ as *mut c_void,
            &mut len as *mut libc::socklen_t,
        );

        assert!(result.is_ok());
        assert_eq!(value, libc::AF_INET);
        assert_eq!(len, size_of::<c_int>() as libc::socklen_t);
    }

    #[test]
    fn write_to_ptr_null_buffer() {
        let domain = SocketDomain::AfInet;
        let mut len = size_of::<c_int>() as libc::socklen_t;

        let result = domain.write_to_ptr(core::ptr::null_mut(), &mut len as *mut libc::socklen_t);

        assert_eq!(result, Err(-1));
    }

    #[test]
    fn write_to_ptr_insufficient_len() {
        let domain = SocketDomain::AfInet;
        let mut value: c_int = 0;
        let mut insufficient_len = (size_of::<c_int>() - 1) as libc::socklen_t;

        let result = domain.write_to_ptr(
            &mut value as *mut _ as *mut c_void,
            &mut insufficient_len as *mut libc::socklen_t,
        );

        assert_eq!(result, Err(-1));
    }
}
