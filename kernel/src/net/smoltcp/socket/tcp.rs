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
    net_manager::NetworkManager,
    socket::{
        socket_err::SocketError, socket_waker, AcceptResult, AcceptedSocket, FnRecv,
        FnRecvWithEndpoint, FnSend, FnSendMsg, PosixSocket,
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
    socket::tcp::{self, State},
    wire::{IpAddress, IpEndpoint, IpListenEndpoint},
};

use crate::net::smoltcp::iface::NetIface;

pub struct TcpSocket {
    socket_fd: SocketFd,
    socket_domain: SocketDomain,
    is_shutdown: Rc<Cell<bool>>,
    network_manager: Rc<RefCell<NetworkManager>>,
    smoltcp_socket_handle: Option<SocketHandle>,
    smoltcp_interface: Option<Arc<NetIface>>,
}

impl TcpSocket {
    pub fn new(
        network_manager: Rc<RefCell<NetworkManager>>,
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

        let tcp_socket = {
            let tcp_rx_buffer = tcp::SocketBuffer::new(vec![0; 1024]);
            let tcp_tx_buffer = tcp::SocketBuffer::new(vec![0; 1024]);
            tcp::Socket::new(tcp_rx_buffer, tcp_tx_buffer)
        };

        // Save socket handle via NetIface::add_socket
        if let Some(socket_handle) = interface.add_socket(tcp_socket) {
            self.smoltcp_socket_handle.replace(socket_handle);
            Some(socket_handle)
        } else {
            None
        }
    }

    pub fn with<F, R>(&mut self, f: F) -> Result<R, SocketError>
    where
        F: FnOnce(&mut tcp::Socket<'static>, &mut Interface) -> Result<R, SocketError>,
    {
        match &self.smoltcp_interface {
            Some(iface) => {
                let handle = self
                    .smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?;
                iface.with_socket::<tcp::Socket<'static>, F, R>(handle, f)
            }
            None => Err(SocketError::InterfaceNoAvailable),
        }
    }

    fn wait_for_accept(
        &mut self,
        accepted_fd: SocketFd,
        local_endpoint: IpListenEndpoint,
        accepted_connection: Arc<crate::net::connection::Connection>,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> AcceptResult {
        if is_nonblocking {
            return Err(SocketError::TryAgain);
        }

        let accept_operation = Operation::Accept {
            socket_fd: self.socket_fd,
            accepted_fd,
            local_endpoint,
            accepted_connection,
            is_nonblocking,
            ipc_reply: ipc_reply.clone(),
        };
        let waker = socket_waker::create_closure_waker(
            "TCP accept()".into(),
            Some(accept_operation),
            self.is_shutdown.clone(),
        );
        self.with(|socket, _| {
            socket.register_recv_waker(&waker);
            Ok(())
        })?;

        Err(SocketError::WouldBlock)
    }
}

impl PosixSocket for TcpSocket {
    fn bind_interface(&mut self, interface: Arc<NetIface>) {
        // Save interface
        self.smoltcp_interface.replace(interface.clone());
    }

    fn accept(
        &mut self,
        accepted_fd: SocketFd,
        local_endpoint: IpListenEndpoint,
        accepted_connection: Arc<crate::net::connection::Connection>,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> AcceptResult {
        let (state, local_endpoint_connected, remote_endpoint) = self.with(|socket, _| {
            Ok((
                socket.state(),
                socket.local_endpoint(),
                socket.remote_endpoint(),
            ))
        })?;

        match state {
            State::Listen | State::SynReceived => {
                return self.wait_for_accept(
                    accepted_fd,
                    local_endpoint,
                    accepted_connection,
                    is_nonblocking,
                    ipc_reply,
                );
            }
            State::Established | State::CloseWait => {}
            _ => {
                return Err(SocketError::InvalidState(format!(
                    "TCP state[{}] cannot accept a connection",
                    state
                )));
            }
        }

        let remote_endpoint = remote_endpoint.ok_or_else(|| {
            SocketError::InvalidState("accepted socket has no remote endpoint".into())
        })?;
        let local_endpoint_connected = local_endpoint_connected.ok_or_else(|| {
            SocketError::InvalidState("accepted socket has no local endpoint".into())
        })?;
        let interface = self
            .smoltcp_interface
            .clone()
            .ok_or(SocketError::InterfaceNoAvailable)?;
        let old_handle = self
            .smoltcp_socket_handle
            .take()
            .ok_or(SocketError::InvalidHandle)?;

        // The established handle becomes the accepted socket. The listening fd gets
        // a fresh handle so it remains usable for the next connection.
        let new_listener_handle = match self.create_smoltcp_socket() {
            Some(handle) => handle,
            None => {
                self.smoltcp_socket_handle = Some(old_handle);
                return Err(SocketError::CreateSmoltcpSocketFail);
            }
        };

        let listen_result = self.with(|socket, _| {
            socket
                .listen(local_endpoint)
                .map_err(SocketError::SmoltcpTcpListenError)
        });
        if let Err(error) = listen_result {
            interface.remove_socket(new_listener_handle);
            self.smoltcp_socket_handle = Some(old_handle);
            return Err(error);
        }

        let mut accepted_socket = TcpSocket::new(
            self.network_manager.clone(),
            accepted_fd,
            self.socket_domain,
        );
        accepted_socket.smoltcp_interface = Some(interface);
        accepted_socket.smoltcp_socket_handle = Some(old_handle);

        Ok(AcceptedSocket {
            socket: Rc::new(RefCell::new(accepted_socket)),
            local_endpoint: local_endpoint_connected,
            remote_endpoint,
        })
    }

    // TCP bind() : TCP Server side method, create smoltcp socket for tcp server
    fn bind(&mut self, _local_endpoint: IpListenEndpoint) -> SocketResult {
        match self.create_smoltcp_socket() {
            Some(_) => Ok(0),
            None => Err(SocketError::CreateSmoltcpSocketFail),
        }
    }

    // TCP connect() : TCP Client side method, create smoltcp socket for tcp client
    fn connect(
        &mut self,
        remote_endpoint: IpEndpoint,
        local_port: u16,
        _is_nonblocking: bool,
    ) -> SocketResult {
        // Create smoltcp socket
        let socket_handle = match self.create_smoltcp_socket() {
            Some(handle) => handle,
            None => return Err(SocketError::CreateSmoltcpSocketFail),
        };

        self.with(|socket, interface| {
            // match socket type
            socket
                .connect(interface.context(), remote_endpoint, local_port)
                .map(|_| 0)
                .map_err(SocketError::SmoltcpTcpConnectError)
        })
    }

    fn listen(&mut self, local_endpoint: IpListenEndpoint) -> SocketResult {
        self.with(|socket, _| {
            if socket.is_active() {
                return Err(SocketError::InvalidState("Socket is active.".into()));
            }

            if socket.is_listening() {
                return Err(SocketError::InvalidState("Socket is listening".into()));
            }

            log::debug!("Listening on {:#?} ", local_endpoint);

            socket
                .listen(local_endpoint)
                .map(|()| 0)
                .map_err(SocketError::SmoltcpTcpListenError)
        })
    }

    fn send(
        &mut self,
        f: FnSend,
        _flag: i32,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        let socket_fd = self.socket_fd;
        let is_shutdown = self.is_shutdown.clone();

        self.with(|socket, _| {
            if socket.can_send() {
                return socket.send(f).map_err(SocketError::SmoltcpTcpSendError);
            }

            match socket.state() {
                State::SynSent | State::SynReceived | State::CloseWait | State::Established => {
                    if !is_nonblocking {
                        let wait_operation = Operation::Send {
                            socket_fd,
                            f,
                            is_nonblocking,
                            ipc_reply,
                        };
                        let socket_operation = Some(wait_operation);
                        let waker = socket_waker::create_closure_waker(
                            "TCP Send()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_send_waker(&waker);
                        log::debug!(
                            "tcp socket not ready for send={:?}, send_queue={:?}",
                            socket.state(),
                            socket.send_queue()
                        );
                        Err(SocketError::WouldBlock)
                    } else {
                        Err(SocketError::TryAgain)
                    }
                }
                _ => {
                    let msg = format!("Invalid TCP state[{}] to send", socket.state());
                    Err(SocketError::InvalidState(msg))
                }
            }
        })
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
            SocketType::SockStream,
            "use send() instead".into(),
        ))
    }

    fn sendmsg(
        &mut self,
        _remote_endpoint: IpEndpoint,
        _identifier: Option<u16>,
        _packet_len: usize,
        _f: FnSendMsg,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockStream,
            "use send() instead".into(),
        ))
    }

    fn recv(
        &mut self,
        f: FnRecv,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        let socket_fd = self.socket_fd;
        let is_shutdown = self.is_shutdown.clone();

        self.with(|socket, _| {
            if socket.can_recv() {
                return socket.recv(f).map_err(SocketError::SmoltcpTcpRecvError);
            }

            match socket.state() {
                State::Closed | State::CloseWait => {
                    let msg = format!(
                        "TCP state[{}]: closed by server, returning 0 to indicate EOF",
                        socket.state()
                    );
                    log::debug!("{}", msg);
                    Ok(0)
                }
                State::SynSent | State::SynReceived | State::Established => {
                    if is_nonblocking {
                        // O_NONBLOCK is set, so return immediately without blocking
                        Err(SocketError::TryAgain)
                    } else {
                        let recv_ops = Operation::Recv {
                            socket_fd,
                            f,
                            is_nonblocking,
                            ipc_reply,
                        };
                        let socket_operation = Some(recv_ops);
                        let recv_waker = socket_waker::create_closure_waker(
                            "TCP recv()".into(),
                            socket_operation,
                            is_shutdown,
                        );
                        socket.register_recv_waker(&recv_waker);
                        log::debug!(
                            "TCP state[{:?}]: no data for recv, recv_queue={:?}",
                            socket.state(),
                            socket.recv_queue()
                        );
                        Err(SocketError::WouldBlock)
                    }
                }
                _ => {
                    // States like FinWait1, FinWait2, or LastAck are unexpected for recv() here
                    let msg = format!("TCP state[{}]: invalid state for recv()", socket.state());
                    log::debug!("{}", msg);
                    Err(SocketError::InvalidState(msg))
                }
            }
        })
    }

    fn recvmsg(
        &mut self,
        _f: FnRecvWithEndpoint,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockStream,
            "use recv() instead".into(),
        ))
    }

    fn recvfrom(
        &mut self,
        _f: FnRecvWithEndpoint,
        _is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult {
        Err(SocketError::UnsupportedSocketTypeForOperation(
            SocketType::SockStream,
            "use recv() instead".into(),
        ))
    }

    fn shutdown(&self) -> SocketResult {
        self.is_shutdown.set(true);

        match &self.smoltcp_interface {
            Some(iface) => {
                let handle = self
                    .smoltcp_socket_handle
                    .ok_or(SocketError::InvalidHandle)?;
                // Close the socket first
                let _ = iface.with_socket::<tcp::Socket<'static>, _, i32>(handle, |socket, _| {
                    socket.close();
                    Ok(0i32)
                });
                // Remove from socket set
                iface.remove_socket(handle);
                Ok(0)
            }
            None => Err(SocketError::InterfaceNoAvailable),
        }
    }

    fn getsockname(
        &mut self,
        f: Box<dyn FnOnce(smoltcp::wire::IpEndpoint) + Send>,
    ) -> SocketResult {
        let socket_domain = self.socket_domain;
        self.with(|socket, _| {
            let local_endpoint = socket.local_endpoint();
            match local_endpoint {
                Some(endpoint) => f(endpoint),
                None => {
                    // Ref to posix getsocketname, still return Ok(0)
                    // If the socket has not been bound to a local name,
                    //  the value stored in the object pointed to by address is unspecified.
                    let address = match socket_domain {
                        SocketDomain::AfInet => IpAddress::Ipv4(Ipv4Addr::UNSPECIFIED),
                        SocketDomain::AfInet6 => IpAddress::Ipv6(Ipv6Addr::UNSPECIFIED),
                    };
                    f(IpEndpoint::new(address, 0))
                }
            };
            Ok(0)
        })
    }

    fn getpeername(
        &mut self,
        f: Box<dyn FnOnce(smoltcp::wire::IpEndpoint) + Send>,
    ) -> SocketResult {
        let socket_domain = self.socket_domain;
        self.with(|socket, _| {
            let remote_endpoint = socket.remote_endpoint();
            match remote_endpoint {
                Some(endpoint) => f(endpoint),
                None => {
                    if socket.state() == tcp::State::Closed {
                        return Err(SocketError::PosixError(
                            -libc::ENOTCONN,
                            "Tcp socket is no connected".into(),
                        ));
                    } else {
                        // Ref to posix getsocketname, still return Ok(0)
                        // If the protocol permits connections by unbound clients,
                        //  and the peer is not bound, then the value stored in the object pointed to by address is unspecified.
                        let address = match socket_domain {
                            SocketDomain::AfInet => IpAddress::Ipv4(Ipv4Addr::UNSPECIFIED),
                            SocketDomain::AfInet6 => IpAddress::Ipv6(Ipv6Addr::UNSPECIFIED),
                        };
                        f(IpEndpoint::new(address, 0));
                    }
                }
            }
            Ok(0)
        })
    }

    fn is_shutdown(&self) -> bool {
        self.is_shutdown.get()
    }
}
