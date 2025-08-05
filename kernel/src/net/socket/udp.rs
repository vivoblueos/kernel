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

use crate::net::{
    connection::{Operation, OperationIPCReply, OperationResult},
    net_interface::NetInterface,
    net_manager::NetworkManager,
    socket::{
        socket_err::SocketError, socket_waker, FnRecv, FnRecvWithEndpoint, FnSend, FnSendMsg,
        PosixSocket,
    },
    SocketDomain, SocketFd, SocketProtocol, SocketResult, SocketType,
};
use alloc::{boxed::Box, format, rc::Rc, sync::Arc, vec};
use core::{
    cell::{Cell, RefCell},
    net::{Ipv4Addr, Ipv6Addr, SocketAddr},
    sync::atomic::AtomicUsize,
};
use smoltcp::{
    iface::{Interface, SocketHandle},
    socket::{icmp::Endpoint, udp},
    wire::{IpAddress, IpEndpoint, IpListenEndpoint},
};
pub struct UdpSocket<'a> {
    socket_fd: SocketFd,
    socket_domain: SocketDomain,
    is_shutdown: Rc<Cell<bool>>,
    network_manager: Rc<RefCell<NetworkManager<'a>>>,
    smoltcp_socket_handle: Option<SocketHandle>,
    smoltcp_interface: Option<Rc<RefCell<NetInterface<'a>>>>,
}

impl<'a> UdpSocket<'a>
where
    'a: 'static,
{
    pub fn new(
        network_manager: Rc<RefCell<NetworkManager<'a>>>,
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
    ) -> Self {
        let is_shutdown = Cell::new(false);

        Self {
            socket_fd,
            socket_domain,
            is_shutdown: Rc::new(is_shutdown),
            network_manager,
            smoltcp_socket_handle: None,
            smoltcp_interface: None,
        }
    }

    fn create_smoltcp_socket(&mut self) -> Option<SocketHandle> {
        let interface = match &self.smoltcp_interface {
            Some(interface) => interface.clone(),
            None => return None,
        };

        // Create smoltcp udp::socket
        let udp_socket = {
            let udp_rx_buffer =
                udp::PacketBuffer::new(vec![udp::PacketMetadata::EMPTY], vec![0; 1024]);
            let udp_tx_buffer =
                udp::PacketBuffer::new(vec![udp::PacketMetadata::EMPTY], vec![0; 1024]);
            udp::Socket::new(udp_rx_buffer, udp_tx_buffer)
        };

        // Save socket handle
        let mut interface = interface.borrow_mut();
        if let Some(socket_handle) = interface.add_socket(udp_socket) {
            self.smoltcp_socket_handle.replace(socket_handle);
            Some(socket_handle)
        } else {
            None
        }
    }

    pub fn with<F>(&mut self, f: F) -> SocketResult
    where
        F: FnOnce(&mut udp::Socket<'a>, &mut Interface) -> SocketResult,
    {
        if let Some(interface) = &self.smoltcp_interface {
            let mut interface = interface.borrow_mut();
            let socket_sets = interface.socket_sets_mut();
            let mut socket_sets = socket_sets.borrow_mut();

            let socket = socket_sets.get_mut::<udp::Socket>(
                self.smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?,
            );

            f(socket, &mut interface.inner_interface_mut().borrow_mut())
        } else {
            Err(SocketError::InterfaceNoAvailable)
        }
    }
}

impl PosixSocket for UdpSocket<'static> {
    fn bind_interface(&mut self, interface: Rc<RefCell<NetInterface<'static>>>) {
        self.smoltcp_interface.replace(interface.clone());
    }

    fn accept(&self, _local_endpoint: IpListenEndpoint) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "accept()".into(),
        ))
    }

    // UDP Server create socket in bind()
    fn bind(&mut self, local_endpoint: IpListenEndpoint) -> SocketResult {
        let socket_handle = self
            .create_smoltcp_socket()
            .ok_or(SocketError::CreateSmoltcpSocketFail)?;

        self.with(|socket, _| match socket.is_open() {
            false => {
                log::debug!("binding on {:#?}", local_endpoint);
                socket
                    .bind(local_endpoint)
                    .map(|()| 1)
                    .map_err(SocketError::SmoltcpUdpBindError)
            }
            true => Err(SocketError::InvalidState("UDP Socket is open.".into())),
        })
    }

    fn connect(
        &mut self,
        _remote_endpoint: IpEndpoint,
        _local_port: u16,
        _is_nonblocking: bool,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "connect()".into(),
        ))
    }

    fn listen(&mut self, _local_endpoint: IpListenEndpoint) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "listen()".into(),
        ))
    }

    fn send(
        &mut self,
        _f: FnSend,
        _flag: i32,
        _is_nonblocking: bool,
        _ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "use sendto() instead".into(),
        ))
    }

    fn sendto(
        &mut self,
        message: &'static [u8],
        _flag: i32,
        remote_endpoint: IpEndpoint,
        local_port: Option<u16>,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        // Create smoltcp socket when no socket handle
        if self.smoltcp_socket_handle.is_none() {
            let _ = self.create_smoltcp_socket();
        }
        let socket_fd = self.socket_fd;
        let is_shutdown = self.is_shutdown.clone();

        self.with(|socket, _| {
            // Bind to local port while socket is not bound
            if let Some(local_port) = local_port {
                log::debug!("binding on {}", local_port);
                socket
                    .bind(local_port)
                    .map_err(SocketError::SmoltcpUdpBindError)?;
            }

            match socket.can_send() {
                true => {
                    let meta_data = udp::UdpMetadata::from(remote_endpoint);
                    log::debug!(
                        "handle_msg_socket udp sendto endpoint {:#?}",
                        remote_endpoint
                    );
                    socket
                        .send_slice(message, meta_data)
                        // udp data send as a whole packet
                        .map(|()| message.len())
                        .map_err(SocketError::SmoltcpUdpSendError)
                }
                false => {
                    if !is_nonblocking {
                        let wait_operation = Operation::SendTo {
                            socket_fd,
                            remote_endpoint,
                            local_port,
                            buffer: message,
                            is_nonblocking,
                            ipc_reply,
                        };
                        let socket_operation = Some(wait_operation);
                        let waker = socket_waker::create_closure_waker(
                            "UDP Sendto()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_send_waker(&waker);
                        log::debug!(
                            "blocking : udp socket not ready for send_queue={:?}",
                            socket.send_queue()
                        );
                        Err(SocketError::WouldBlock)
                    } else {
                        // O_NONBLOCK is set for return immediately,
                        // UDP is state-less socket , always return EAGAIN
                        log::debug!(
                            "nonblocking: udp socket buffer not ready for send_queue={:?}",
                            socket.send_queue()
                        );
                        Err(SocketError::TryAgain)
                    }
                }
            }
        })
    }

    fn sendmsg(
        &mut self,
        _remote_endpoint: IpEndpoint,
        _identifer: Option<u16>,
        _packet_len: usize,
        _f: FnSendMsg,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "use sendto() instead".into(),
        ))
    }

    fn recv(
        &mut self,
        _f: FnRecv,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "use recvfrom() instead".into(),
        ))
    }

    fn recvmsg(
        &mut self,
        _f: FnRecvWithEndpoint,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "use recvfrom() instead".into(),
        ))
    }

    fn recvfrom(
        &mut self,
        f: FnRecvWithEndpoint,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        let socket_fd = self.socket_fd;
        let is_shutdown = self.is_shutdown.clone();

        self.with(|socket, _| {
            match socket.can_recv() {
                true => socket
                    .recv()
                    .map(|(recv_buffer, udp_meta_data)| f(recv_buffer, udp_meta_data.endpoint))
                    .map_err(SocketError::SmoltcpUdpRecvError),
                false => {
                    if !is_nonblocking {
                        let wait_operation = Operation::RecvFrom {
                            socket_fd,
                            f,
                            is_nonblocking,
                            ipc_reply,
                        };

                        let socket_operation = Some(wait_operation);
                        let waker = socket_waker::create_closure_waker(
                            "UDP recvfrom()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_recv_waker(&waker);
                        log::debug!(
                            "blocking : no data for udp recvfrom recv_queue={:?}",
                            socket.recv_queue()
                        );
                        Err(SocketError::WouldBlock)
                    } else {
                        // O_NONBLOCK is set for return immediately,
                        // UDP is state-less socket , always return EAGAIN
                        log::debug!(
                            "nonblocking : no data for udp recvfrom recv_queue={:?}",
                            socket.recv_queue()
                        );
                        Err(SocketError::TryAgain)
                    }
                }
            }
        })
    }

    fn shutdown(&self) -> SocketResult {
        self.is_shutdown.set(true);

        if let Some(interface) = &self.smoltcp_interface {
            let mut interface = interface.borrow_mut();
            let socket_sets = interface.socket_sets_mut();
            let mut socket_sets = socket_sets.borrow_mut();

            let socket = socket_sets.get_mut::<udp::Socket>(
                self.smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?,
            );

            socket.close();

            let _ = socket_sets.remove(
                self.smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?,
            );
            Ok(0)
        } else {
            Err(SocketError::InvalidState("shutdown".into()))
        }
    }

    fn getsockname(&mut self, f: Box<dyn FnOnce(IpEndpoint) + Send>) -> SocketResult {
        let socket_domain = self.socket_domain;
        self.with(|socket, _| {
            // Try to get endpoint from socket
            let local_endpoint = socket.endpoint();
            let address = match local_endpoint.addr {
                Some(address) => address,
                None => {
                    // None means binding to any address
                    match socket_domain {
                        SocketDomain::AfInet => IpAddress::Ipv4(Ipv4Addr::UNSPECIFIED),
                        SocketDomain::AfInet6 => IpAddress::Ipv6(Ipv6Addr::UNSPECIFIED),
                    }
                }
            };
            f(IpEndpoint::new(address, local_endpoint.port));
            Ok(0)
        })
    }

    fn getpeername(&mut self, f: Box<dyn FnOnce(IpEndpoint) + Send>) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockDgram,
            "UDP socket do not support getpeername()".into(),
        ))
    }

    fn is_shutdown(&self) -> bool {
        self.is_shutdown.get()
    }
}
