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

use alloc::{boxed::Box, string::String, sync::Arc, vec};
use blueos::{
    allocator,
    net::{self, SocketAddress, SocketAddressV4, SocketAddressV6, SocketDomain, SocketMsghdr},
    scheduler,
    sync::atomic_wait as futex,
    thread::Builder as ThreadBuilder,
    time::Tick,
};
use blueos_test_macro::test;
use core::{
    ffi::c_void,
    fmt::Debug,
    mem,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};
use libc::{AF_INET, AF_INET6};
use semihosting::println;

use crate::net::{net_utils, net_utils::NetTestArgs};

static ICMP_THREAD_FINISH: AtomicUsize = AtomicUsize::new(0);
fn icmp_thread(args: Arc<NetTestArgs>) {
    println!("Thread enter:[icmp_thread]");

    // Create socket
    let sock_fd = net::syscalls::socket(
        args.domain.into(),
        libc::SOCK_RAW | args.type_flag(),
        args.icmp_protocol_type(),
    );
    assert!(sock_fd >= 0, "Fail to create icmp socket.");

    // Create sockaddr
    let remote_port = 1234;
    let sockaddr_len = match args.domain {
        SocketDomain::AfInet => core::mem::size_of::<libc::sockaddr_in>(),
        SocketDomain::AfInet6 => core::mem::size_of::<libc::sockaddr_in6>(),
    };
    let mut sockaddr_storage: libc::sockaddr_storage = unsafe { core::mem::zeroed() };
    let mut sockaddr_addr = &mut sockaddr_storage as *mut _ as *mut libc::sockaddr;
    match args.domain {
        SocketDomain::AfInet => {
            let remote_ip = "127.0.0.1"; // Replace with actual IP address
            println!(
                "Socket[{}] sending msg to {}:{} addr_len={}",
                sock_fd, remote_ip, remote_port, sockaddr_len
            );
            net_utils::write_ipv4_sockaddr(
                sockaddr_addr as *mut libc::sockaddr_in,
                remote_ip,
                remote_port,
            );
        }
        SocketDomain::AfInet6 => {
            println!(
                "Socket[{}] sending msg to ::1:{} addr_len={}",
                sock_fd, remote_port, sockaddr_len
            );
            net_utils::write_ipv6_local_sockaddr(
                sockaddr_addr as *mut libc::sockaddr_in6,
                remote_port,
            );
        }
    };

    let (icmp_echo_packet_ptr, icmp_echo_packet_len) = match args.domain {
        SocketDomain::AfInet => net_utils::create_icmpv4_echo_packet(),
        SocketDomain::AfInet6 => net_utils::create_icmpv6_echo_packet(),
    };

    // Create iov data which store ECHO msg
    let mut iov_payload = libc::iovec {
        iov_base: icmp_echo_packet_ptr as *mut libc::c_void,
        iov_len: icmp_echo_packet_len,
    };

    // Create libc::msghdr structure for send
    let mut msghdr_send: libc::msghdr = unsafe { core::mem::zeroed() };
    msghdr_send.msg_name = sockaddr_addr as *mut libc::c_void;
    msghdr_send.msg_namelen = sockaddr_len as u32;
    msghdr_send.msg_iov = &mut iov_payload as *mut libc::iovec;
    msghdr_send.msg_iovlen = 1;
    msghdr_send.msg_control = core::ptr::null_mut();

    let msg_send_ptr = &msghdr_send as *const libc::msghdr;

    // Send loop
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        let send_bytes = net::syscalls::sendmsg(sock_fd, msg_send_ptr, 0);
        if send_bytes > 0 {
            println!("Socket[{}] send icmp packet bytes={}", sock_fd, send_bytes);
            return true;
        }

        scheduler::yield_me();
        false
    });

    // Warnning!!! Sleep for at least 1s when using ipv6 with Midum::Ethernet,
    //    while smoltcp neigbor cache has limit on access rate.

    // Create recv address buffer
    let mut sockaddr_storage: libc::sockaddr_storage = unsafe { core::mem::zeroed() };
    let mut sockaddr_addr = &mut sockaddr_storage as *mut _ as *mut libc::sockaddr;

    // Create recv iov buffer
    const IOV_BUFFER_LEN: usize = 128;
    let mut iov_buffer = [0u8; IOV_BUFFER_LEN];
    let mut iov_payload = libc::iovec {
        iov_base: iov_buffer.as_mut_ptr() as *mut libc::c_void,
        iov_len: IOV_BUFFER_LEN as libc::size_t,
    };

    // Create libc::msghdr structure for recv
    let mut msghdr_recv = libc::msghdr {
        msg_name: sockaddr_addr as *mut libc::c_void,
        msg_namelen: sockaddr_len as u32,
        msg_iov: &mut iov_payload as *mut libc::iovec,
        msg_iovlen: 1,
        msg_control: core::ptr::null_mut(),
        msg_controllen: 0,
        msg_flags: 0,
    };
    let msg_recv_ptr = &mut msghdr_recv as *mut libc::msghdr;

    // Recv loop
    let mut recv_bytes = 0;
    let domain = args.domain;
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        recv_bytes = net::syscalls::recvmsg(sock_fd, msg_recv_ptr, 0);
        if recv_bytes > 0 {
            println!("Socket[{}] recv icmp packet bytes={}", sock_fd, recv_bytes);
            let msg_recv = unsafe { &*msg_recv_ptr };

            // print data
            match net_utils::read_bytes_from_iov(
                msg_recv.msg_iov,
                msg_recv.msg_iovlen as usize,
                recv_bytes as usize,
            ) {
                Ok(recv_packet) => {
                    net_utils::println_hex(recv_packet.as_slice(), recv_packet.len())
                }
                Err(e) => println!("Socket[{}] recv data fail: {}", sock_fd, e),
            }

            // print address
            match unsafe {
                SocketAddress::from_ptr(
                    msg_recv.msg_name as *const libc::sockaddr,
                    msg_recv.msg_namelen,
                )
            } {
                Some(addr) => match addr.create_ip_endpoint() {
                    Some(ep) => println!("Socket[{}] recv icmp packet from = {:#?}", sock_fd, ep),
                    None => println!("Socket[{}] create ip endpoint fail", sock_fd),
                },
                None => {
                    println!("Socket[{}] recv icmp packet from: unknown address", sock_fd)
                }
            }

            return true; // stop loop
        }

        scheduler::yield_me();
        false
    });

    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    println!("Socket[{}] shutdown result {}", sock_fd, shutdown_result);

    assert!(recv_bytes > 0, "Test icmp socket fail.");
    println!("Thread exit:[icmp_thread]");
}

#[test]
fn test_icmp_ipv4() {
    ICMP_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: false,
    });

    net_utils::start_test_thread_with_cleanup(
        "icmp_thread",
        Box::new(move || {
            icmp_thread(args);
        }),
        Some(Box::new(|| {
            ICMP_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&ICMP_THREAD_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&ICMP_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_icmp_ipv4_non_blocking() {
    ICMP_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: true,
    });

    net_utils::start_test_thread_with_cleanup(
        "icmp_thread",
        Box::new(move || {
            icmp_thread(args);
        }),
        Some(Box::new(|| {
            ICMP_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&ICMP_THREAD_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&ICMP_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_icmp_ipv6() {
    ICMP_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: false,
    });

    net_utils::start_test_thread_with_cleanup(
        "icmp_thread",
        Box::new(move || {
            icmp_thread(args);
        }),
        Some(Box::new(|| {
            ICMP_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&ICMP_THREAD_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&ICMP_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_icmp_ipv6_non_blocking() {
    ICMP_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: true,
    });

    net_utils::start_test_thread_with_cleanup(
        "icmp_thread",
        Box::new(move || {
            icmp_thread(args);
        }),
        Some(Box::new(|| {
            ICMP_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&ICMP_THREAD_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&ICMP_THREAD_FINISH, 0, Tick::MAX);
}
