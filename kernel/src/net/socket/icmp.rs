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
    connection::{Operation, OperationIPCReply},
    net_interface::NetInterface,
    net_manager::NetworkManager,
    socket::{
        socket_err::SocketError, socket_waker, FnRecv, FnRecvWithEndpoint, FnSend, FnSendMsg,
        PosixSocket,
    },
    SocketFd, SocketResult, SocketType,
};
use alloc::{boxed::Box, rc::Rc, sync::Arc, vec};
use core::{
    cell::{Cell, RefCell},
    net::{SocketAddr, SocketAddrV4, SocketAddrV6},
};
use smoltcp::{
    iface::{Interface, SocketHandle},
    socket::icmp,
    wire::{IpEndpoint, IpListenEndpoint},
};
pub struct IcmpSocket<'a> {
    socket_fd: SocketFd,
    is_shutdown: Rc<Cell<bool>>,
    network_manager: Rc<RefCell<NetworkManager<'a>>>,
    smoltcp_socket_handle: Option<SocketHandle>,
    smoltcp_interface: Option<Rc<RefCell<NetInterface<'a>>>>,
}

impl<'a> IcmpSocket<'a>
where
    'a: 'static,
{
    pub fn new(network_manager: Rc<RefCell<NetworkManager<'a>>>, socket_fd: SocketFd) -> Self {
        let is_shutdown = Cell::new(false);
        Self {
            socket_fd,
            is_shutdown: Rc::new(is_shutdown),
            network_manager,
            smoltcp_socket_handle: None,
            smoltcp_interface: None,
        }
    }

    fn create_smoltcp_socket(&mut self) -> Option<SocketHandle> {
        if let Some(socket_handle) = self.smoltcp_socket_handle {
            return Some(socket_handle);
        }

        // Get Interface
        let interface = match &self.smoltcp_interface {
            Some(interface) => interface.clone(),
            None => return None,
        };

        // Create smoltcp icmp::socket
        let icmp_socket = {
            let icmp_rx_buffer =
                icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
            let icmp_tx_buffer =
                icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
            icmp::Socket::new(icmp_rx_buffer, icmp_tx_buffer)
        };

        // Save socket handle
        let mut interface = interface.borrow_mut();
        if let Some(socket_handle) = interface.add_socket(icmp_socket) {
            self.smoltcp_socket_handle.replace(socket_handle);
            Some(socket_handle)
        } else {
            None
        }
    }

    fn with<F>(&mut self, f: F) -> SocketResult
    where
        F: FnOnce(&mut icmp::Socket<'a>, &mut Interface) -> SocketResult,
    {
        if let Some(interface) = &self.smoltcp_interface {
            let mut interface = interface.borrow_mut();
            let socket_sets = interface.socket_sets_mut();
            let mut socket_sets = socket_sets.borrow_mut();

            let socket = socket_sets.get_mut::<icmp::Socket>(
                self.smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?,
            );

            f(socket, &mut interface.inner_interface_mut().borrow_mut())
        } else {
            Err(SocketError::InterfaceNoAvailable)
        }
    }
}

impl PosixSocket for IcmpSocket<'static> {
    fn bind_interface(&mut self, interface: Rc<RefCell<NetInterface<'static>>>) {
        // Save interface
        self.smoltcp_interface.replace(interface.clone());
    }

    fn accept(&self, _local_endpoint: IpListenEndpoint) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "accept()".into(),
        ))
    }

    // ICMP Server create socket in bind()
    fn bind(&mut self, local_endpoint: IpListenEndpoint) -> SocketResult {
        let socket_handle = self
            .create_smoltcp_socket()
            .ok_or(SocketError::CreateSmoltcpSocketFail)?;

        self.with(|socket, _| match socket.is_open() {
            false => {
                log::debug!("binding icmp socket on endpoint:{:#?}", local_endpoint);
                socket
                    .bind(icmp::Endpoint::Udp(local_endpoint))
                    .map(|()| 0)
                    .map_err(SocketError::SmoltcpIcmpBindError)
            }
            true => Err(SocketError::InvalidState("ICMP socket is open.".into())),
        })
    }

    fn connect(
        &mut self,
        _remote_endpoint: IpEndpoint,
        _local_port: u16,
        _is_nonblocking: bool,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "connect()".into(),
        ))
    }

    fn listen(&mut self, _local_endpoint: IpListenEndpoint) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
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
            SocketType::SockRaw,
            "use sendmsg() instead".into(),
        ))
    }

    fn sendto(
        &mut self,
        _message: &'static [u8],
        _flag: i32,
        _remote_endpoint: IpEndpoint,
        _local_port: Option<u16>,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "use sendmsg() instead".into(),
        ))
    }

    fn sendmsg(
        &mut self,
        remote_endpoint: IpEndpoint,
        identifer: Option<u16>,
        packet_len: usize,
        f: FnSendMsg,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        // Create smoltcp socket when no socket handle
        let socket_handle = match self.smoltcp_socket_handle {
            Some(socket_handlle) => socket_handlle,
            None => self
                .create_smoltcp_socket()
                .ok_or(SocketError::CreateSmoltcpSocketFail)?,
        };

        let socket_fd = self.socket_fd;
        let is_shutdown = self.is_shutdown.clone();
        self.with(|socket, _| {
            if !socket.is_open() {
                match identifer {
                    Some(identifer) => {
                        log::debug!("Icmp socket bind identifier={}", identifer);
                        socket
                            .bind(icmp::Endpoint::Ident(identifer))
                            .map_err(SocketError::SmoltcpIcmpBindError)?
                    }
                    None => {
                        log::debug!("Icmp socket is not open and find no identifier");
                        return Err(SocketError::InvalidState("find no identifer".into()));
                    }
                }
            }

            match socket.can_send() {
                true => {
                    log::debug!("Icmp socket sendmsg");
                    socket
                        .send_with(packet_len, remote_endpoint.addr, f)
                        .map_err(SocketError::SmoltcpIcmpSendError)
                }
                false => {
                    if !is_nonblocking {
                        let wait_operation = Operation::SendMsg {
                            socket_fd,
                            remote_endpoint,
                            identifer,
                            packet_len,
                            f,
                            is_nonblocking,
                            ipc_reply,
                        };
                        let socket_operation = Some(wait_operation);
                        let waker = socket_waker::create_closure_waker(
                            "ICMP SendMsg()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_send_waker(&waker);
                        log::debug!(
                            "icmp socket not ready for send_queue={:?}",
                            socket.send_queue()
                        );
                        Err(SocketError::WouldBlock)
                    } else {
                        // O_NONBLOCK is set for return immediately,
                        // ICMP is state-less socket , always return EAGAIN
                        log::debug!(
                            "nonblocking: icmp socket buffer not ready for send_queue={:?}",
                            socket.send_queue()
                        );
                        Err(SocketError::TryAgain)
                    }
                }
            }
        })
    }

    fn recv(
        &mut self,
        _f: FnRecv,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "use recvmsg() instead".into(),
        ))
    }

    fn recvmsg(
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
                    .map(|(payload, addr)| f(payload, (addr, 0).into()))
                    .map_err(SocketError::SmoltcpIcmpRecvError),
                false => {
                    if !is_nonblocking {
                        let wait_operation = Operation::RecvMsg {
                            socket_fd,
                            f,
                            is_nonblocking,
                            ipc_reply,
                        };
                        let socket_operation = Some(wait_operation);
                        let waker = socket_waker::create_closure_waker(
                            "ICMP recvmsg()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_recv_waker(&waker);
                        log::debug!(
                            "no data for icmp recvmsg recv_queue={:?}",
                            socket.recv_queue()
                        );
                        Err(SocketError::WouldBlock)
                    } else {
                        // O_NONBLOCK is set for return immediately,
                        // ICMP is state-less socket , always return EAGAIN
                        log::debug!(
                            "nonblocking: icmp socket buffer not ready for recv_queue={:?}",
                            socket.recv_queue()
                        );
                        Err(SocketError::TryAgain)
                    }
                }
            }
        })
    }

    fn recvfrom(
        &mut self,
        _f: FnRecvWithEndpoint,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "use recvmsg() instead".into(),
        ))
    }

    fn shutdown(&self) -> SocketResult {
        self.is_shutdown.set(true);

        if let Some(interface) = &self.smoltcp_interface {
            let mut interface = interface.borrow_mut();
            let socket_sets = interface.socket_sets_mut();
            let mut socket_sets = socket_sets.borrow_mut();

            let _ = socket_sets.remove(
                self.smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?,
            );

            Ok(0)
        } else {
            Err(SocketError::InvalidState("shutdown".into()))
        }
    }

    fn getsockname(
        &mut self,
        f: Box<dyn FnOnce(smoltcp::wire::IpEndpoint) + Send>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "icmp not support getsockname".into(),
        ))
    }

    fn getpeername(
        &mut self,
        f: Box<dyn FnOnce(smoltcp::wire::IpEndpoint) + Send>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockRaw,
            "icmp not support getpeername".into(),
        ))
    }

    fn is_shutdown(&self) -> bool {
        self.is_shutdown.get()
    }
}
