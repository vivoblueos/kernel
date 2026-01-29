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
    net::{self, SocketAddress, SocketDomain},
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

static UDP_SERVER_THREAD_FINISH: AtomicUsize = AtomicUsize::new(0);
static UDP_CLIENT_THREAD_FINISH: AtomicUsize = AtomicUsize::new(0);

fn udp_server_thread(args: Arc<NetTestArgs>) {
    println!("Thread enter:[udp_server_thread]");

    // Create socket
    let sock_fd = net::syscalls::socket(args.domain.into(), libc::SOCK_DGRAM | args.type_flag(), 0);
    assert!(sock_fd >= 0, "Fail to create udp server socket fd.");

    // Bind socket
    let local_ip = "127.0.0.1"; // Replace with actual IP address
    let local_port = 1234;
    let bind_result = match args.domain {
        SocketDomain::AfInet => {
            let addr_ipv4 = net_utils::create_ipv4_sockaddr(local_ip, local_port);
            println!("Socket[{}] binding {}:{}", sock_fd, local_ip, local_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv4 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
        SocketDomain::AfInet6 => {
            let addr_ipv6 = net_utils::create_ipv6_local_sockaddr(local_port);
            println!("Socket[{}] binding ::1:{}", sock_fd, local_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv6 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
    };
    println!("Socket[{}] bind result {}", sock_fd, bind_result);
    assert!(bind_result == 0, "Failed to bind udp server socket.");

    // Start client thread
    let client_args = args.clone();
    net_utils::start_test_thread_with_cleanup(
        "udp_client_thread",
        Box::new(move || {
            udp_client_thread(client_args);
        }),
        Some(Box::new(|| {
            UDP_CLIENT_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&UDP_CLIENT_THREAD_FINISH, 1);
        })),
    );

    // Start listening
    let mut buffer = vec![0u8; 1024];
    let mut addr: libc::sockaddr_in6 = unsafe { mem::zeroed() }; // allocate a bigger one
    let mut addr_len: libc::socklen_t = unsafe { mem::zeroed() };
    let mut bytes_received = 0;

    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        let addr_ptr = &mut addr as *mut _ as *mut libc::sockaddr;
        let addr_len_ptr = &mut addr_len as *mut libc::socklen_t;

        bytes_received = net::syscalls::recvfrom(
            sock_fd,
            buffer.as_mut_ptr() as *mut c_void,
            buffer.len(),
            0,
            addr_ptr,
            addr_len_ptr,
        );

        if bytes_received > 0 {
            let received_size = bytes_received as usize;
            println!("Socket[{}] recv {} bytes", sock_fd, bytes_received);

            // Try to convert using String::from_utf8
            match String::from_utf8(buffer[0..received_size].to_vec()) {
                Ok(text) => println!("Socket[{}] recv UDP text: {}", sock_fd, text),
                Err(e) => println!("Socket[{}] recv UDP text fail: {}", sock_fd, e),
            }

            // Hex print section
            net_utils::println_hex(buffer.as_slice(), received_size);

            // print socket addr
            let _ = unsafe {
                SocketAddress::from_ptr(addr_ptr as *const libc::sockaddr, *addr_len_ptr)
            }
            .and_then(|addr| addr.create_ip_endpoint())
            .map(|e| println!("Socket[{}] Recv UDP packet from ={:#?}", sock_fd, e))
            .or_else(|| {
                println!("Socket[{}] Recv UDP packet from no endpoint", sock_fd);
                None
            });

            return true;
        }
        scheduler::yield_me();
        false
    });

    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    println!("Socket[{}] shutdown result {}", sock_fd, shutdown_result);
    assert!(
        shutdown_result == 0,
        "Failed to shutdown udp server socket."
    );

    UDP_SERVER_THREAD_FINISH.store(1, Ordering::Release);
    let _ = futex::atomic_wake(&UDP_SERVER_THREAD_FINISH, 1);
    assert!(bytes_received > 0, "Test udp server recv fail.");

    println!("Thread exit:[udp_server_thread]");
}

fn udp_client_thread(args: Arc<NetTestArgs>) {
    println!("Thread enter:[udp_client_thread]");

    // Create socket
    let sock_fd = net::syscalls::socket(args.domain.into(), libc::SOCK_DGRAM | args.type_flag(), 0);
    assert!(sock_fd >= 0, "Fail to create udp client socket fd.");

    // Connect socket
    let local_ip = "127.0.0.1"; // Replace with actual IP address
    let local_port = 1235;
    let bind_result = match args.domain {
        SocketDomain::AfInet => {
            let addr_ipv4 = net_utils::create_ipv4_sockaddr(local_ip, local_port);
            println!("Socket[{}] binding {}:{}", sock_fd, local_ip, local_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv4 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
        SocketDomain::AfInet6 => {
            let addr_ipv6 = net_utils::create_ipv6_local_sockaddr(local_port);
            println!("Socket[{}] binding ::1:{}", sock_fd, local_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv6 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
    };
    println!("Socket[{}] bind result {}", sock_fd, bind_result);
    assert!(bind_result == 0, "Failed to bind udp client socket.");

    let message = "Hello From Posix UDP client";
    let bytes = message.as_bytes();

    // Prepare remote IP address and port
    let remote_addr = "127.0.0.1"; // Replace with actual IP address
    let remote_port = 1234;

    let mut bytes_sent = 0;
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        // Call send function to send data
        bytes_sent = match args.domain {
            SocketDomain::AfInet => {
                let remote_endpoint = net_utils::create_ipv4_sockaddr(remote_addr, remote_port);
                net::syscalls::sendto(
                    sock_fd,
                    bytes.as_ptr() as *const c_void,
                    bytes.len(),
                    0,
                    &remote_endpoint as *const _ as *const libc::sockaddr,
                    mem::size_of::<libc::sockaddr>() as libc::socklen_t,
                )
            }
            SocketDomain::AfInet6 => {
                let remote_endpoint = net_utils::create_ipv6_local_sockaddr(remote_port);
                net::syscalls::sendto(
                    sock_fd,
                    bytes.as_ptr() as *const c_void,
                    bytes.len(),
                    0,
                    &remote_endpoint as *const _ as *const libc::sockaddr,
                    mem::size_of::<libc::sockaddr>() as libc::socklen_t,
                )
            }
        };
        println!("Socket[{}] send {} bytes", sock_fd, bytes_sent);

        // Handle send result
        if bytes_sent > 0 {
            println!("Socket[{}] sent message: {}", sock_fd, message);

            if bytes_sent as usize != bytes.len() {
                println!(
                    "Socket[{}] Warning: Only sent partial data ({}/{} bytes)",
                    sock_fd,
                    bytes_sent,
                    bytes.len()
                );
            }
            return true;
        }

        scheduler::yield_me();
        false
    });
    assert!(bytes_sent > 0, "Test udp client send fail.");

    let _ = futex::atomic_wait(&UDP_SERVER_THREAD_FINISH, 0, Tick::MAX);
    // Warning!!! Shutdown after server thread exit, or server may not able to recv data from client
    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    assert!(
        shutdown_result == 0,
        "Failed to shutdown udp client socket."
    );

    println!("Thread exit:[udp_client_thread]");
}

#[test]
fn test_udp_ipv4() {
    UDP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    UDP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: false,
    });

    net_utils::start_test_thread(
        "udp_server_thread",
        Box::new(move || {
            udp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&UDP_CLIENT_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_udp_ipv4_non_blocking() {
    println!("Enter test_udp_ipv4_non_blocking");
    UDP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    UDP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: true,
    });

    net_utils::start_test_thread(
        "udp_server_thread",
        Box::new(move || {
            udp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&UDP_CLIENT_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_udp_ipv6() {
    UDP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    UDP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: false,
    });

    net_utils::start_test_thread(
        "udp_server_thread",
        Box::new(move || {
            udp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&UDP_CLIENT_THREAD_FINISH, 0, Tick::MAX);
}

#[test]
fn test_udp_ipv6_non_blocking() {
    UDP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    UDP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: true,
    });

    net_utils::start_test_thread(
        "udp_server_thread",
        Box::new(move || {
            udp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&UDP_CLIENT_THREAD_FINISH, 0, Tick::MAX);
}
