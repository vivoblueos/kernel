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

// This code is based on https://github.com/smoltcp-rs/smoltcp/blob/main/examples/loopback.rs:
// Copyright (C) smoltcp contributors
// SPDX-LICENSE: 0BSD

use super::net_utils;
use alloc::{boxed::Box, vec, vec::Vec};
use blueos::{
    allocator, net, scheduler,
    sync::atomic_wait as futex,
    thread::{Builder as ThreadBuilder, Entry, Stack},
    time::Tick,
};
use blueos_test_macro::test;
use byteorder::{ByteOrder, NetworkEndian};
use core::{
    str,
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::{c_void, AF_INET};
use semihosting::println;
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{Device, Loopback, Medium},
    socket::{icmp, icmp::Endpoint, tcp},
    time::{Duration, Instant},
    wire::{
        EthernetAddress, Icmpv4Packet, Icmpv4Repr, Icmpv6Packet, Icmpv6Repr, IpAddress, IpCidr,
    },
};

mod mock {
    use core::cell::Cell;
    use smoltcp::time::{Duration, Instant};

    #[derive(Debug)]
    pub struct Clock(Cell<Instant>);

    impl Clock {
        pub fn new() -> Clock {
            Clock(Cell::new(Instant::from_millis(0)))
        }

        pub fn advance(&self, duration: Duration) {
            self.0.set(self.0.get() + duration)
        }

        pub fn elapsed(&self) -> Instant {
            self.0.get()
        }
    }
}

pub type NetThreadFn = extern "C" fn(arg: *mut core::ffi::c_void);

static SMOLTCP_TEST_DONE: AtomicUsize = AtomicUsize::new(0);
static ICMP_LOOPBACK_TEST_DONE: AtomicUsize = AtomicUsize::new(0);

// Run smoltcp socket test on loopback device.
// WARNING: Do not run this test in the main thread to prevent stack overflow.
fn smoltcp_test_thread() {
    let clock = mock::Clock::new();
    let mut device = Loopback::new(Medium::Ethernet);

    println!("[smoltcp Tcp Socket Test]: Create interface with loopback device");
    // Create interface
    let config = match device.capabilities().medium {
        Medium::Ethernet => {
            Config::new(EthernetAddress([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]).into())
        }
        Medium::Ip => Config::new(smoltcp::wire::HardwareAddress::Ip),
        Medium::Ieee802154 => todo!(),
    };

    let mut iface = Interface::new(config, &mut device, Instant::from_millis(0));
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8))
            .unwrap();
    });

    println!("[smoltcp Tcp Socket Test]: Create sockets");
    // Create sockets
    let server_socket = {
        // It is not strictly necessary to use a `static mut` and unsafe code here, but
        // on embedded systems that smoltcp targets it is far better to allocate the data
        // statically to verify that it fits into RAM rather than get undefined behavior
        // when stack overflows.
        static mut TCP_SERVER_RX_DATA: [u8; 1024] = [0; 1024];
        static mut TCP_SERVER_TX_DATA: [u8; 1024] = [0; 1024];
        let tcp_rx_buffer = tcp::SocketBuffer::new(unsafe { &mut TCP_SERVER_RX_DATA[..] });
        let tcp_tx_buffer = tcp::SocketBuffer::new(unsafe { &mut TCP_SERVER_TX_DATA[..] });
        tcp::Socket::new(tcp_rx_buffer, tcp_tx_buffer)
    };

    let client_socket = {
        static mut TCP_CLIENT_RX_DATA: [u8; 1024] = [0; 1024];
        static mut TCP_CLIENT_TX_DATA: [u8; 1024] = [0; 1024];
        let tcp_rx_buffer = tcp::SocketBuffer::new(unsafe { &mut TCP_CLIENT_RX_DATA[..] });
        let tcp_tx_buffer = tcp::SocketBuffer::new(unsafe { &mut TCP_CLIENT_TX_DATA[..] });
        tcp::Socket::new(tcp_rx_buffer, tcp_tx_buffer)
    };

    let mut sockets: [_; 2] = Default::default();
    let mut sockets = SocketSet::new(&mut sockets[..]);
    let server_handle = sockets.add(server_socket);
    let client_handle = sockets.add(client_socket);

    let mut did_listen = false;
    let mut did_connect = false;
    let mut done = false;

    println!("[smoltcp Tcp Socket Test]: Enter poll device loop");
    while !done && clock.elapsed() < Instant::from_millis(10_000) {
        iface.poll(clock.elapsed(), &mut device, &mut sockets);

        let socket = sockets.get_mut::<tcp::Socket>(server_handle);
        if !socket.is_active() && !socket.is_listening() && !did_listen {
            println!("[smoltcp Tcp Socket Test]: Socket listening");
            socket.listen(1234).unwrap();
            did_listen = true;
        }

        if socket.can_recv() {
            println!(
                "[smoltcp Tcp Socket Test]: Socket recv {:?}",
                socket.recv(|buffer| { (buffer.len(), str::from_utf8(buffer).unwrap()) })
            );
            socket.close();
            done = true;
        }

        let socket = sockets.get_mut::<tcp::Socket>(client_handle);
        let cx = iface.context();
        if !socket.is_open() && !did_connect {
            println!("[smoltcp Tcp Socket Test]: Socket connecting");
            socket
                .connect(cx, (IpAddress::v4(127, 0, 0, 1), 1234), 65000)
                .unwrap();
            did_connect = true;
        }

        if socket.can_send() {
            println!("[smoltcp Tcp Socket Test]: Socket sending 0123456789abcdef");
            socket.send_slice(b"0123456789abcdef").unwrap();
            socket.close();
        }

        match iface.poll_delay(clock.elapsed(), &sockets) {
            Some(Duration::ZERO) => println!("[smoltcp Tcp Socket Test]: iface resuming"),
            Some(delay) => {
                println!(
                    "[smoltcp Tcp Socket Test]: Inteface poll sleeping for {} ms",
                    delay
                );
                clock.advance(delay);
                println!("[smoltcp Tcp Socket Test]: after advance")
            }
            None => clock.advance(Duration::from_millis(1)),
        }
    }

    assert!(
        done,
        "[smoltcp Tcp Socket Test]: Bailing out: socket test took too long on loopback device"
    );
}

// Run smoltcp socket test on loopback device
fn smoltcp_test_thread_icmp() {
    println!("Enter test_icmp_loopback");
    let clock = mock::Clock::new();
    let mut device = Loopback::new(Medium::Ethernet);
    let device_caps = device.capabilities();

    println!("Create interface with loopback device");
    // Create interface
    let mut config = match device.capabilities().medium {
        Medium::Ethernet => {
            Config::new(EthernetAddress([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]).into())
        }
        Medium::Ip => Config::new(smoltcp::wire::HardwareAddress::Ip),
        Medium::Ieee802154 => todo!(),
    };

    let mut iface = Interface::new(config, &mut device, Instant::from_millis(0));
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8))
            .unwrap();
        ip_addrs
            .push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128))
            .unwrap();
    });

    // let remote_addr = IpAddress::v4(127, 0, 0, 1);
    // let remote_addr = IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1);

    println!("Create sockets");
    // Create sockets
    let icmp_rx_buffer = icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
    let icmp_tx_buffer = icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
    let icmp_socket = icmp::Socket::new(icmp_rx_buffer, icmp_tx_buffer);
    let mut sockets = SocketSet::new(vec![]);
    let icmp_handle = sockets.add(icmp_socket);

    let mut send_at = Instant::from_millis(0);
    let mut seq_no = 0;
    let mut received = 0;
    let mut echo_payload = [0xffu8; 40];
    let ident = 0x22b;

    let mut done = false;

    static ECHO_PACKET_BYTES: [u8; 12] = [
        0x08, // type     : u8    ECHO = 8
        0x00, // code     : u8
        0x8e, 0xfe, // checksum : u16
        0x02, 0x2b, // identifer: u16   BigEndian , ident   = 0x22b
        0x00, 0x00, // sequence : u16   BinEndian , seq_no  = 0
        0xaa, 0x00, 0x00, 0xff, // data : Vec<u8>
    ];
    // For socket api test
    // Create a libc::msghdr
    let mut sockaddr_in_obj = net_utils::create_ipv4_sockaddr("127.0.0.1", 1234);
    let (icmp_echo_packet_ptr, packet_len) = net_utils::create_icmpv4_echo_packet();
    let mut iovec_obj = libc::iovec {
        iov_base: icmp_echo_packet_ptr as *mut c_void,
        iov_len: packet_len,
    };

    let mut msghdr_obj = libc::msghdr {
        msg_name: &mut sockaddr_in_obj as *mut libc::sockaddr_in as *mut libc::c_void,
        msg_namelen: core::mem::size_of::<libc::sockaddr_in>() as u32,
        msg_iov: &mut iovec_obj as *mut libc::iovec,
        msg_iovlen: 1,
        msg_control: core::ptr::null_mut(),
        msg_controllen: 0,
        msg_flags: 0,
    };

    // let mut msghdr_obj = create_icmp_msghdr("127.0.0.1", 1234);
    let (remote_endpoint, icmp_packet_vec) =
        net_utils::parse_msghdr(AF_INET, &msghdr_obj as *const libc::msghdr).unwrap();
    let remote_endpoint = remote_endpoint.unwrap();
    let remote_addr = remote_endpoint.addr;

    let compare_vec = Vec::from(ECHO_PACKET_BYTES);
    net_utils::println_hex(compare_vec.as_slice(), compare_vec.len());
    net_utils::println_hex(icmp_packet_vec.as_slice(), icmp_packet_vec.len());

    println!("Enter poll device loop");
    while !done && clock.elapsed() < Instant::from_millis(500) {
        iface.poll(clock.elapsed(), &mut device, &mut sockets);

        let mut icmp_socket = sockets.get_mut::<icmp::Socket>(icmp_handle);

        if !icmp_socket.is_open() {
            println!("icmp_socket.bind ");
            icmp_socket.bind(icmp::Endpoint::Ident(ident)).unwrap();
        }

        // send
        if icmp_socket.can_send() {
            println!("icmp_socket.can_send addr {:#?} ", remote_addr);
            NetworkEndian::write_i64(&mut echo_payload, clock.elapsed().total_micros());

            match remote_addr {
                IpAddress::Ipv4(_) => {
                    let icmp_repr = Icmpv4Repr::EchoRequest {
                        ident,
                        seq_no,
                        data: &echo_payload,
                    };

                    let size = icmp_socket
                        // .send_with(icmp_repr.buffer_len(), remote_addr, |packet| {
                        .send_with(icmp_packet_vec.len(), remote_addr, |packet| {
                            // let mut icmp_package = Icmpv4Packet::new_unchecked(packet);
                            // icmp_repr.emit(&mut icmp_package, &device_caps.checksum);
                            // icmp_repr.buffer_len()

                            // packet.copy_from_slice(&ECHO_PACKET_BYTES);
                            packet.copy_from_slice(icmp_packet_vec.as_slice());
                            icmp_packet_vec.len()
                        })
                        .unwrap();
                }
                IpAddress::Ipv6(address) => {
                    let icmp_repr = Icmpv6Repr::EchoRequest {
                        ident,
                        seq_no,
                        data: &echo_payload,
                    };

                    let icmp_payload = icmp_socket
                        .send(icmp_repr.buffer_len(), remote_addr)
                        .unwrap();

                    let mut icmp_packet = Icmpv6Packet::new_unchecked(icmp_payload);

                    icmp_repr.emit(
                        &iface.get_source_address_ipv6(&address),
                        &address,
                        &mut icmp_packet,
                        &device_caps.checksum,
                    );
                }
            }

            seq_no += 1;
        }

        // recv
        if icmp_socket.can_recv() {
            println!("icmp_socket.can_recv ");

            let (payload, addr) = icmp_socket.recv().unwrap();
            println!("icmp_socket recv() addr={}", addr);

            match remote_addr {
                IpAddress::Ipv4(_) => {
                    let icmp_packet = Icmpv4Packet::new_checked(&payload).unwrap();
                    let vec_payload = Vec::from(payload);
                    net_utils::println_hex(vec_payload.as_slice(), vec_payload.len());
                    let icmp_repr = Icmpv4Repr::parse(&icmp_packet, &device_caps.checksum).unwrap();
                    println!("icmp_socket icmpv4 recv() icmp_repr={}", icmp_repr);

                    if let Icmpv4Repr::EchoReply { seq_no, data, .. } = icmp_repr {
                        let packet_timestamp_ms = NetworkEndian::read_i64(data);
                        println!(
                            "recived ipv4 from network : {} bytes from {}: icmp_seq={}",
                            data.len(),
                            remote_addr,
                            seq_no
                        );
                    }
                    done = true
                }
                IpAddress::Ipv6(address) => {
                    let icmp_packet = Icmpv6Packet::new_checked(&payload).unwrap();
                    let icmp_repr = Icmpv6Repr::parse(
                        &address,
                        &iface.get_source_address_ipv6(&address),
                        &icmp_packet,
                        &device_caps.checksum,
                    )
                    .unwrap();
                    println!("icmp_socket icmpv6 recv() icmp_repr={:#?}", icmp_repr);

                    if let Icmpv6Repr::EchoReply { seq_no, data, .. } = icmp_repr {
                        let packet_timestamp_ms = NetworkEndian::read_i64(data);
                        println!(
                            "recived ipv6 from network : {} bytes from {}: icmp_seq={}",
                            data.len(),
                            remote_addr,
                            seq_no
                        );
                    }
                    done = true
                }
            }
        }

        let timestamp = clock.elapsed();
        match iface.poll_at(timestamp, &sockets) {
            Some(poll_at) if timestamp < poll_at => {
                println!("poll_at timestamp < poll_at {}", poll_at);
            }
            Some(v) => {
                println!("poll_at Some({})", v);
            }
            None => {
                println!("poll_at None");
            }
        }

        clock.advance(Duration::from_millis(50));
    }

    if done {
        println!("Finish : test icmp on loopback device.")
    } else {
        println!("Bailing out : this is taking too long.")
    }
}

#[test]
fn test_smoltcp() {
    SMOLTCP_TEST_DONE.store(0, Ordering::Release);

    net_utils::start_test_thread_with_cleanup(
        "smoltcp_test_thread",
        Box::new(move || {
            smoltcp_test_thread();
        }),
        Some(Box::new(|| {
            SMOLTCP_TEST_DONE.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&SMOLTCP_TEST_DONE, 1);
        })),
    );
    let _ = futex::atomic_wait(&SMOLTCP_TEST_DONE, 0, Tick::MAX);
}

#[test]
fn test_smoltcp_icmp_loopback() {
    ICMP_LOOPBACK_TEST_DONE.store(0, Ordering::Release);

    net_utils::start_test_thread_with_cleanup(
        "test_icmp_loopback",
        Box::new(move || {
            smoltcp_test_thread_icmp();
        }),
        Some(Box::new(|| {
            ICMP_LOOPBACK_TEST_DONE.store(1, Ordering::Release);
            let _ = futex::atomic_wake(&ICMP_LOOPBACK_TEST_DONE, 1);
        })),
    );
    let _ = futex::atomic_wait(&ICMP_LOOPBACK_TEST_DONE, 0, Tick::MAX);
}
