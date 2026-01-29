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

//! Socket test with qemu virtio net device
//!
//! To run the test, we need a tcp server running on other machine , here is a simple server :
//! ## A simple server test script in Node.js
//! ```javascript
//! const net = require('net');
//!
//! const server = net.createServer((socket) => {
//!   console.log('Client connected!');
//!
//!   socket.on('data', (data) => {
//!     console.log(`Recived from client: ${data.toString()}`);
//!     socket.write('Hello from Server!'); // Reply to client
//!   });
//!
//!   socket.on('end', () => {
//!     console.log('Client disconnected!');
//!   });
//!
//!   socket.on('error', (err) => {
//!     console.error(`Client error: ${err.message}`);
//!   });
//! });
//!
//! server.on('error', (err) => {
//!   console.error(`Server error: ${err.message}`);
//! });
//!
//! server.listen(3000, () => {
//!   console.log('Server listening on port 3000');
//! });
//! ```
//!
//! ## Usage Instructions
//! 1. Save as `test_server.js`
//! 2. Install Node.js: https://nodejs.org
//! 3. Run: `node test_server.js`
//! 4. Run test_virtio_net_device() test
//!

use crate::net::{net_utils, net_utils::NetTestArgs};
use alloc::{boxed::Box, string::String, sync::Arc, vec};
use blueos::{
    allocator, net,
    net::SocketDomain,
    scheduler,
    sync::atomic_wait as futex,
    thread::{Builder as ThreadBuilder, Entry, Stack},
    time::Tick,
};
use blueos_test_macro::test;
use core::{
    ffi::c_void,
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::sockaddr_storage;
use semihosting::println;
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    socket::tcp,
    time::{Duration, Instant},
    wire::{EthernetAddress, IpAddress, IpCidr, Ipv4Address},
};

static VIRTIO_NET_CLIENT_FINISH: AtomicUsize = AtomicUsize::new(0);
fn virtio_net_client(args: Arc<NetTestArgs>) {
    println!("Thread enter:[virtio_net_client]");

    // Create socket
    let sock_fd =
        net::syscalls::socket(args.domain.into(), libc::SOCK_STREAM | args.type_flag(), 0);
    assert!(sock_fd >= 0, "Fail to create virtio-net tcp client socket.");

    // Connect to host server at 10.58.54.123:3000
    // In QEMU user networking, the host is accessible via 10.0.2.2
    // let remote_addr = (Ipv4Address::new(10, 0, 2, 2), 5001);
    // Window Subsystem Linux
    let remote_addr = "10.58.54.123"; // Replace with actual IP address
    let remote_port = 3000;

    let mut sockaddr_buffer: libc::sockaddr_in = unsafe { core::mem::zeroed() };
    let mut sockaddr_addr = &mut sockaddr_buffer as *mut libc::sockaddr_in;
    net_utils::write_ipv4_sockaddr(sockaddr_addr, remote_addr, remote_port);
    let mut sockaddr_len = core::mem::size_of::<libc::sockaddr_in>();

    // Convert sockaddr_in to sockaddr and call connect
    let connect_result = net::syscalls::connect(
        sock_fd,
        sockaddr_addr as *const libc::sockaddr,
        sockaddr_len as libc::socklen_t,
    );
    println!("Socket[{}] connect result {}", sock_fd, connect_result);

    let message = "Hello From Posix Virtio Net Client";
    let bytes = message.as_bytes();

    let mut bytes_sent = 0;
    net_utils::loop_with_io_mode(!args.is_nonblocking, || {
        // Call send function to send data
        bytes_sent = net::syscalls::send(sock_fd, bytes.as_ptr() as *const c_void, bytes.len(), 0);

        // Handle send result
        if bytes_sent >= 0 {
            println!(
                "Socket[{}] Successfully sent {} bytes of data",
                sock_fd, bytes_sent
            );
            println!("Socket[{}] Sent message: {}", sock_fd, message);

            if bytes_sent as usize != bytes.len() {
                println!(
                    "Socket[{}] Warning: Only sent partial data ({}/{} bytes)",
                    sock_fd,
                    bytes_sent,
                    bytes.len()
                );
            }
            return true;
        } else {
            println!("Socket[{}] Failed to send data", sock_fd);
        }

        scheduler::yield_me();
        false
    });

    // Create read buffer
    let mut buffer = vec![0u8; 1024];

    if bytes_sent > 0 {
        let mut bytes_received = 0;
        net_utils::loop_with_io_mode(!args.is_nonblocking, || {
            bytes_received =
                net::syscalls::recv(sock_fd, buffer.as_mut_ptr() as *mut c_void, buffer.len(), 0);

            if bytes_received > 0 {
                let received_size = bytes_received as usize;
                println!(
                    "Socket[{}] Received {} bytes of data",
                    sock_fd, bytes_received
                );

                // Try to convert using String::from_utf8
                match String::from_utf8(buffer[0..received_size].to_vec()) {
                    Ok(text) => println!("Socket[{}] Received text: {}", sock_fd, text),
                    Err(_) => println!("Socket[{}] Received data is not valid UTF-8 text", sock_fd),
                }

                // Hex print section
                net_utils::println_hex(&buffer, received_size);
                return true;
            }

            scheduler::yield_me();
            false
        });
    }

    let shutdown_result = net::syscalls::shutdown(sock_fd, 0);
    println!("Socket[{}] shutdown result {}", sock_fd, shutdown_result);
    assert!(
        shutdown_result == 0,
        "Failed to shutdown virtio-net tcp client socket."
    );

    println!("Thread exit:[virtio_net_client]");
}

// Blocking call may block test thread while we has no timeout until now.
// #[test]
fn test_virtio_net() {
    VIRTIO_NET_CLIENT_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: false,
    });

    net_utils::start_test_thread_with_cleanup(
        "virtio_net_client",
        Box::new(move || {
            virtio_net_client(args);
        }),
        Some(Box::new(|| {
            VIRTIO_NET_CLIENT_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&VIRTIO_NET_CLIENT_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&VIRTIO_NET_CLIENT_FINISH, 0, Tick::MAX);
}

#[test]
fn test_virtio_net_non_blocking() {
    VIRTIO_NET_CLIENT_FINISH.store(0, Ordering::Release);

    let args = Arc::new(NetTestArgs {
        domain: SocketDomain::AfInet,
        is_nonblocking: true,
    });

    net_utils::start_test_thread_with_cleanup(
        "virtio_net_client",
        Box::new(move || {
            virtio_net_client(args);
        }),
        Some(Box::new(|| {
            VIRTIO_NET_CLIENT_FINISH.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&VIRTIO_NET_CLIENT_FINISH, 1);
        })),
    );

    let _ = futex::atomic_wait(&VIRTIO_NET_CLIENT_FINISH, 0, Tick::MAX);
}
