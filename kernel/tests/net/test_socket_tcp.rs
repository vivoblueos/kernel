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
    net::{self, SocketDomain},
    scheduler,
    sync::atomic_wait as futex,
    thread::Builder as ThreadBuilder,
};
use blueos_test_macro::test;
use core::{
    cmp,
    ffi::c_void,
    fmt::Debug,
    mem,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};
use libc::{AF_INET, AF_INET6};
use semihosting::println;

use crate::net::{net_utils, net_utils::NetTestArgs};

static TCP_SERVER_THREAD_FINISH: AtomicUsize = AtomicUsize::new(0);
static TCP_CLIENT_THREAD_FINISH: AtomicUsize = AtomicUsize::new(0);

fn tcp_server_thread(args: Arc<NetTestArgs>) {
    println!("Thread enter:[tcp_server_thread]");

    // Create socket
    let sock_fd =
        net::syscalls::socket(args.domain.into(), libc::SOCK_STREAM | args.type_flag(), 0);
    assert!(sock_fd >= 0, "Fail to create tcp server socket.");

    // Bind socket
    let listen_ip = "127.0.0.1"; // Replace with actual IP address
    let listen_port = 1234;
    let bind_result = match args.domain {
        SocketDomain::AfInet => {
            let addr_ipv4 = net_utils::create_ipv4_sockaddr(listen_ip, listen_port);
            println!("Socket[{}] binding {}:{}", sock_fd, listen_ip, listen_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv4 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
        SocketDomain::AfInet6 => {
            let addr_ipv6 = net_utils::create_ipv6_local_sockaddr(listen_port);
            println!("Socket[{}] binding ::1:{}", sock_fd, listen_port);
            net::syscalls::bind(
                sock_fd,
                &addr_ipv6 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
    };
    println!("Socket[{}] bind result {}", sock_fd, bind_result);
    assert!(bind_result == 0, "Failed to bind on tcp server socket.");

    // Start listening
    let listen_result = net::syscalls::listen(sock_fd, 0);
    println!("Socket[{}] listen result {}", sock_fd, listen_result);
    assert!(listen_result == 0, "Failed to listen on tcp server socket.");

    // Start client thread
    let client_args = args.clone();
    net_utils::start_test_thread_with_cleanup(
        "tcp_client_thread",
        Box::new(move || {
            tcp_client_thread(client_args);
        }),
        Some(Box::new(|| {
            TCP_CLIENT_THREAD_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&TCP_CLIENT_THREAD_FINISH, 1);
        })),
    );

    let mut buffer = vec![0u8; 1024];
    let mut received_text = false;
    let mut received_eof = false;
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        let mut bytes_received =
            net::syscalls::recv(sock_fd, buffer.as_mut_ptr() as *mut c_void, buffer.len(), 0);
        println!("Socket[{}] recv {} bytes", sock_fd, bytes_received);

        match bytes_received.cmp(&0) {
            cmp::Ordering::Greater => {
                let received_size = bytes_received as usize;

                // Attempt to convert received bytes to UTF-8 string (lossy to avoid errors)
                let text = String::from_utf8_lossy(&buffer[..received_size]);
                println!("Socket[{}] recv TCP text: {}", sock_fd, text);

                // Print received data in hex format
                net_utils::println_hex(&buffer[..received_size], received_size);

                received_text = true;
            }
            cmp::Ordering::Less => {
                println!(
                    "Socket[{}] unexpected bytes_received={}",
                    sock_fd, bytes_received
                );
                if received_text {
                    // Exit the test loop once text is received to avoid EOF wait timeout
                    return true;
                }
            }
            cmp::Ordering::Equal => {
                // bytes_received == 0 means EOF
                println!("Socket[{}] recv TCP EOF", sock_fd);
                received_eof = true;
                return true; // Indicate EOF received
            }
        }

        scheduler::yield_me();
        false
    });

    assert!(
        received_text || received_eof,
        "Failed to receive data or EOF."
    );

    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    println!("Socket[{}] shutdown result {}", sock_fd, shutdown_result);
    assert!(
        shutdown_result == 0,
        "Failed to shutdown tcp server socket."
    );

    TCP_SERVER_THREAD_FINISH.store(1, Ordering::Release);
    let _ = futex::atomic_wake(&TCP_SERVER_THREAD_FINISH, 1);
    println!("Thread exit:[tcp_server_thread]");
}

fn tcp_client_thread(args: Arc<NetTestArgs>) {
    println!("Thread enter:[tcp_client_thread]");

    // Create socket
    let sock_fd =
        net::syscalls::socket(args.domain.into(), libc::SOCK_STREAM | args.type_flag(), 0);
    assert!(sock_fd >= 0, "Fail to create tcp client socket.");

    // Connect socket
    let remote_ip = "127.0.0.1"; // Replace with actual IP address
    let remote_port = 1234;
    let connect_result = match args.domain {
        SocketDomain::AfInet => {
            let addr_ipv4 = net_utils::create_ipv4_sockaddr(remote_ip, remote_port);
            println!(
                "Socket[{}] connecting {}:{}",
                sock_fd, remote_ip, remote_port
            );
            net::syscalls::connect(
                sock_fd,
                &addr_ipv4 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
        SocketDomain::AfInet6 => {
            let addr_ipv6 = net_utils::create_ipv6_local_sockaddr(remote_port);
            println!("Socket[{}] connecting ::1:{}", sock_fd, remote_port);
            net::syscalls::connect(
                sock_fd,
                &addr_ipv6 as *const _ as *const libc::sockaddr,
                mem::size_of::<libc::sockaddr>() as libc::socklen_t,
            )
        }
    };
    println!("Socket[{}] connect result {}", sock_fd, connect_result);
    assert!(connect_result == 0, "Failed to connect through tcp socket.");

    let message = "Hello From Posix TCP client";
    let bytes = message.as_bytes();

    let mut bytes_sent = 0;
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        bytes_sent = net::syscalls::send(sock_fd, bytes.as_ptr() as *const c_void, bytes.len(), 0);
        println!("Socket[{}] send {} bytes", sock_fd, bytes_sent);

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

    // Call shutdown to send EOF (i.e., close the write side of the socket)
    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    assert!(
        shutdown_result == 0,
        "Failed to shutdown tcp client socket."
    );

    let _ = futex::atomic_wait(&TCP_SERVER_THREAD_FINISH, 0, None);

    assert!(bytes_sent > 0, "Test tcp client send fail.");
    println!("Thread exit:[tcp_client_thread]");
}

#[test]
fn test_tcp_ipv4() {
    TCP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    TCP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: false,
    });

    net_utils::start_test_thread(
        "tcp_server_thread",
        Box::new(move || {
            tcp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&TCP_CLIENT_THREAD_FINISH, 0, None);
}

#[test]
fn test_tcp_ipv4_non_blocking() {
    println!("Enter test_tcp_ipv4_non_blocking");
    TCP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    TCP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: true,
    });

    net_utils::start_test_thread(
        "tcp_server_thread",
        Box::new(move || {
            tcp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&TCP_CLIENT_THREAD_FINISH, 0, None);
}

#[test]
fn test_tcp_ipv6() {
    TCP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    TCP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: false,
    });

    net_utils::start_test_thread(
        "tcp_server_thread",
        Box::new(move || {
            tcp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&TCP_CLIENT_THREAD_FINISH, 0, None);
}

#[test]
fn test_tcp_ipv6_non_blocking() {
    TCP_CLIENT_THREAD_FINISH.store(0, Ordering::Release);
    TCP_SERVER_THREAD_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet6,
        is_nonblocking: true,
    });

    net_utils::start_test_thread(
        "tcp_server_thread",
        Box::new(move || {
            tcp_server_thread(args);
        }),
    );

    let _ = futex::atomic_wait(&TCP_CLIENT_THREAD_FINISH, 0, None);
}
