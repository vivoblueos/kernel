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

use crate::{
    error::{code, Error},
    net::{
        connection_err::ConnectionError,
        net_manager::NetworkManager,
        port_generator::PORT_GENERATOR,
        socket::{
            socket_err::SocketError, FnRecv, FnRecvWithEndpoint, FnSend, FnSendMsg, PosixSocket,
        },
        SocketDomain, SocketFd, SocketProtocol, SocketResult, SocketType,
    },
    scheduler::{self, yield_me},
    sync::atomic_wait as futex,
    thread::Thread,
};
use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::{
    cell::RefCell,
    net::SocketAddr,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    time::Duration,
};
use smoltcp::wire::{IpAddress, IpEndpoint, IpListenEndpoint};
use spin::Mutex;

// For posix syscalls
pub type ConnectionResult = Result<usize, ConnectionError>;

pub struct Connection {
    socket_fd: SocketFd,
    socket_domain: SocketDomain,
    socket_type: SocketType,
    socket_protocol: SocketProtocol,
    local_endpoint: Mutex<Option<IpListenEndpoint>>,
    remote_endpoint: Mutex<Option<IpEndpoint>>,
    is_nonblocking: AtomicBool, // default io mode is blocking, use O_NONBLOCK to set non-blocking
    recv_timeout: Mutex<Option<Duration>>, // block indefinitely as default
    send_timeout: Mutex<Option<Duration>>, // block indefinitely as default
    ipc_reply: Arc<OperationIPCReply>,
}

impl Connection {
    pub fn new(
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
        socket_type: SocketType,
        socket_protocol: SocketProtocol,
    ) -> Self {
        Self {
            socket_fd,
            socket_domain,
            socket_type,
            socket_protocol,
            local_endpoint: Mutex::new(None),
            remote_endpoint: Mutex::new(None),
            is_nonblocking: AtomicBool::new(false),
            recv_timeout: Mutex::new(None),
            send_timeout: Mutex::new(None),
            ipc_reply: Arc::new(OperationIPCReply::new()),
        }
    }

    pub fn set_is_nonblocking(&self, is_nonblocking: bool) {
        self.is_nonblocking.store(is_nonblocking, Ordering::Release);
    }

    pub fn create(&mut self) -> ConnectionResult {
        let create_task = Operation::Create {
            socket_fd: self.socket_fd,
            socket_domain: self.socket_domain,
            socket_type: self.socket_type,
            socket_protocol: self.socket_protocol,
            ipc_reply: self.ipc_reply.clone(),
        };

        log::debug!("[Socket {}] Create request queued", self.socket_fd);

        self.ipc_reply.queue_and_wait(create_task)
    }

    pub fn bind(&self, local_endpoint: IpEndpoint) -> ConnectionResult {
        log::debug!(
            "[Socket {}] Bound to {}:{}",
            self.socket_fd,
            local_endpoint.addr,
            local_endpoint.port
        );

        // TCP / UDP / ICMPv4 / ICMPv6
        if self.socket_type != SocketType::SockRaw
            || self.socket_protocol == SocketProtocol::Icmp
            || self.socket_protocol == SocketProtocol::Icmpv6
        {
            let local_endpoint = {
                let mut endpoint_guard = self.local_endpoint.lock();
                let port = if matches!(
                    self.socket_type,
                    SocketType::SockStream | SocketType::SockDgram
                ) {
                    PORT_GENERATOR.acquire_port(self.socket_type, local_endpoint.port)?
                } else {
                    local_endpoint.port
                };

                let local_endpoint: IpListenEndpoint = (local_endpoint.addr, port).into();
                endpoint_guard.replace(local_endpoint);
                local_endpoint
            };

            let bind_task = Operation::Bind {
                socket_fd: self.socket_fd,
                local_endpoint,
                ipc_reply: self.ipc_reply.clone(),
            };

            log::debug!("[Socket {}] Bind request queued", self.socket_fd);

            // Wait for network stack response and return directly
            self.ipc_reply.queue_and_wait(bind_task)
        } else {
            Err(ConnectionError::UnsupportedSocketType(self.socket_type))
        }
    }

    pub fn listen(&self) -> ConnectionResult {
        let local_endpoint = match *self.local_endpoint.lock() {
            Some(endpoint) => endpoint,
            None => return Err(ConnectionError::LockFail("local endpoint".into())),
        };

        let listen_task = Operation::Listen {
            socket_fd: self.socket_fd,
            local_endpoint,
            ipc_reply: self.ipc_reply.clone(),
        };

        log::debug!("[Socket {}] Listen request queued", self.socket_fd);

        // Wait for network stack response and return directly
        self.ipc_reply.queue_and_wait(listen_task)
    }

    pub fn connect(&self, remote_endpoint: IpEndpoint) -> ConnectionResult {
        // Use binding local_endpoint first , or use 0 to allocate dynamic port
        let local_port = {
            let mut local_endpoint = *self.local_endpoint.lock();
            match local_endpoint {
                Some(endpoint) => endpoint.port,
                None => {
                    let port = PORT_GENERATOR.acquire_port(SocketType::SockStream, 0)?;
                    local_endpoint.replace(port.into());
                    port
                }
            }
        };

        let connect_task = Operation::Connect {
            socket_fd: self.socket_fd,
            remote_endpoint,
            local_port,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        self.remote_endpoint.lock().replace(remote_endpoint);

        log::debug!("[Socket {}] Connect request queued", self.socket_fd);

        self.ipc_reply.queue_and_wait(connect_task)
    }

    pub fn shutdown(&self) -> ConnectionResult {
        // Construct shutdown request with cloned response channel
        let shutdown_task = Operation::Shutdown {
            socket_fd: self.socket_fd,
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] Shutdown request queued", self.socket_fd);

        // Await and return final shutdown status from network stack
        self.ipc_reply.queue_and_wait(shutdown_task)
    }

    pub fn recv(&self, f: FnRecv) -> ConnectionResult {
        // Construct receive request with buffer ownership transfer
        let recv_task = Operation::Recv {
            socket_fd: self.socket_fd,
            f,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] Recv request queued", self.socket_fd);

        // Wait for network stack response and convert result
        self.ipc_reply.queue_and_wait(recv_task)
    }

    pub fn recvfrom(&self, f: FnRecvWithEndpoint) -> ConnectionResult {
        // Construct receive request with buffer ownership transfer
        let recv_task = Operation::RecvFrom {
            socket_fd: self.socket_fd,
            f,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] RecvFrom request queued", self.socket_fd);

        // Wait for network stack response and convert result
        self.ipc_reply.queue_and_wait(recv_task)
    }

    pub fn send(&self, f: FnSend, _flag: i32) -> ConnectionResult {
        // Construct send request with buffer reference
        let send_task = Operation::Send {
            socket_fd: self.socket_fd,
            f,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] Send request queued", self.socket_fd);

        self.ipc_reply.queue_and_wait(send_task)
    }

    pub fn sendto(
        &self,
        message: &'static [u8],
        _flag: i32,
        remote_endpoint: IpEndpoint,
    ) -> ConnectionResult {
        // Allocate dynamic port while not bound in UDP
        let local_port = {
            if self.socket_type == SocketType::SockDgram {
                let mut endpoint = self.local_endpoint.lock();
                if endpoint.is_none() {
                    let local_port = PORT_GENERATOR.acquire_port(self.socket_type, 0)?;
                    endpoint.replace((local_port).into());
                    Some(local_port)
                } else {
                    // endpoint is some() means already bind
                    None
                }
            } else {
                None
            }
        };

        // Construct send request with buffer reference
        let sendto_task = Operation::SendTo {
            socket_fd: self.socket_fd,
            remote_endpoint,
            local_port,
            buffer: message,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!(
            "[Socket {}] SendTo request queued ({} bytes)",
            self.socket_fd,
            message.len()
        );

        self.ipc_reply.queue_and_wait(sendto_task)
    }

    // ICMP/ICMPv6 only now
    pub fn sendmsg(
        &self,
        remote_endpoint: IpEndpoint,
        identifer: Option<u16>,
        packet_len: usize,
        f: FnSendMsg,
    ) -> ConnectionResult {
        // Construct send request with buffer reference
        let sendmsg_task = Operation::SendMsg {
            socket_fd: self.socket_fd,
            remote_endpoint,
            identifer,
            packet_len,
            f,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] SendMsg request queued", self.socket_fd);

        self.ipc_reply.queue_and_wait(sendmsg_task)
    }

    pub fn recvmsg(&self, f: FnRecvWithEndpoint) -> ConnectionResult {
        // Construct send request with buffer reference
        let sendmsg_task = Operation::RecvMsg {
            socket_fd: self.socket_fd,
            f,
            is_nonblocking: self.is_nonblocking.load(Ordering::Acquire),
            ipc_reply: self.ipc_reply.clone(),
        };

        // Log successful request submission
        log::debug!("[Socket {}] RecvMsg request queued", self.socket_fd);

        self.ipc_reply.queue_and_wait(sendmsg_task)
    }

    // Set recv timeout : ref to libc::SO_RCVTIMEO
    pub fn set_recv_timeout(&self, timeout: Duration) {
        self.recv_timeout.lock().replace(timeout);
    }

    // Set send timeout : ref to libc::SO_SNDTIMEO
    pub fn set_send_timeout(&self, timeout: Duration) {
        self.send_timeout.lock().replace(timeout);
    }

    // Get recv timeout : ref to libc::SO_RCVTIMEO
    pub fn get_recv_timeout(&self) -> Duration {
        match *self.recv_timeout.lock() {
            Some(duration) => duration,
            None => Duration::ZERO,
        }
    }

    // Get send timeout : reft to libc::SO_SNDTIMEO
    pub fn get_send_timeout(&self) -> Duration {
        match *self.send_timeout.lock() {
            Some(duration) => duration,
            None => Duration::ZERO,
        }
    }

    pub fn socket_type(&self) -> SocketType {
        self.socket_type
    }

    pub fn socket_domain(&self) -> SocketDomain {
        self.socket_domain
    }

    pub fn socket_protocol(&self) -> SocketProtocol {
        self.socket_protocol
    }

    pub fn is_bound(&self) -> bool {
        self.local_endpoint.lock().is_some()
    }

    pub fn is_connected(&self) -> bool {
        // Client connect or Server bound
        self.remote_endpoint.lock().is_some() || self.local_endpoint.lock().is_some()
    }

    fn with_posix_socket<F: FnOnce(Rc<RefCell<dyn PosixSocket>>) -> Option<OperationResult>>(
        network_manager: Rc<RefCell<NetworkManager<'static>>>,
        socket_fd: i32,
        ipc_reply: Arc<OperationIPCReply>,
        f: F,
    ) {
        if let Some(posix_socket) = network_manager.borrow_mut().get_posix_socket(socket_fd) {
            if posix_socket.borrow().is_shutdown() {
                log::debug!("Socket {} already shutdown", socket_fd);
                return;
            }

            if let Some(result) = f(posix_socket) {
                ipc_reply.wakeup_client(result, socket_fd);
            }
        } else {
            ipc_reply.wakeup_client(Err(SocketError::InvalidSocketFd(socket_fd)), socket_fd);
        }
    }

    pub fn handle_socket_msg(network_manager: Rc<RefCell<NetworkManager<'static>>>) -> bool {
        // one msg at a time , TODO batch
        if let Some(socket_request) = NETSTACK_QUEUE.dequeue() {
            match socket_request {
                Operation::Create {
                    socket_fd,
                    socket_domain,
                    socket_type,
                    socket_protocol,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Create socket_fd={}", socket_fd);

                    let network_manager_ref = network_manager.clone();
                    let _ = network_manager.borrow_mut().create_posix_socket(
                        socket_fd,
                        network_manager_ref,
                        socket_domain,
                        socket_type,
                        socket_protocol,
                    );

                    ipc_reply.wakeup_client(Ok(0), socket_fd);
                }
                Operation::Listen {
                    socket_fd,
                    local_endpoint,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Listen socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            Some(posix_socket.listen(local_endpoint))
                        },
                    )
                }
                Operation::Connect {
                    socket_fd,
                    remote_endpoint,
                    local_port,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Connect socket_fd={}", socket_fd);

                    {
                        // Bind socket when we know remote addr : smoltcp need
                        let network_manager_mut = network_manager.borrow_mut();
                        network_manager_mut.bind_smoltcp_interface(socket_fd, remote_endpoint.addr);
                    }

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();

                            Some(posix_socket.connect(remote_endpoint, local_port, is_nonblocking))
                        },
                    );
                }
                Operation::Shutdown {
                    socket_fd,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Shutdown socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();

                            Some(posix_socket.shutdown())
                        },
                    );
                }
                Operation::Send {
                    socket_fd,
                    f,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Send socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();

                            let result = posix_socket.send(f, 0, is_nonblocking, ipc_reply.clone());

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                    "[Connection] handle Send socket_fd={} , recv 0 data , wait for socket",
                                    socket_fd,
                                );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::SendTo {
                    socket_fd,
                    remote_endpoint,
                    local_port,
                    buffer,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle SendTo socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();

                            let result = posix_socket.sendto(
                                buffer,
                                0,
                                remote_endpoint,
                                local_port,
                                is_nonblocking,
                                ipc_reply.clone(),
                            );

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                    "[Connection] handle SendTo socket_fd={} , blocking wait for socket",
                                    socket_fd,
                                );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::SendMsg {
                    socket_fd,
                    remote_endpoint,
                    identifer,
                    packet_len,
                    f,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle SendMsg socket_fd={}", socket_fd);

                    {
                        let network_manager_mut = network_manager.borrow_mut();
                        network_manager_mut.bind_smoltcp_interface(socket_fd, remote_endpoint.addr);
                    }

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            let result = posix_socket.sendmsg(
                                remote_endpoint,
                                identifer,
                                packet_len,
                                f,
                                is_nonblocking,
                                ipc_reply.clone(),
                            );

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                    "[Connection] handle SendMsg socket_fd={} , blocking wait for socket",
                                    socket_fd,
                                );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::Recv {
                    socket_fd,
                    f,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Recv socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            let result = posix_socket.recv(f, is_nonblocking, ipc_reply.clone());

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                    "[Connection] handle Recv socket_fd={} , blocking wait for socket",
                                    socket_fd,
                                );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::RecvFrom {
                    socket_fd,
                    f,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle RecvFrom socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            let result =
                                posix_socket.recvfrom(f, is_nonblocking, ipc_reply.clone());

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                        "[Connection] handle RecvFrom socket_fd={} , blocking wait for socket",
                                        socket_fd,
                                    );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::RecvMsg {
                    socket_fd,
                    f,
                    is_nonblocking,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle RecvMsg socket_fd={}", socket_fd);

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            let result = posix_socket.recvmsg(f, is_nonblocking, ipc_reply.clone());

                            if let Err(SocketError::WouldBlock) = result.as_ref() {
                                log::debug!(
                                        "[Connection] handle RecvMsg socket_fd={} , blocking wait for socket",
                                        socket_fd,
                                    );
                                None
                            } else {
                                Some(result)
                            }
                        },
                    );
                }
                Operation::Bind {
                    socket_fd,
                    local_endpoint,
                    ipc_reply,
                } => {
                    log::debug!("[Connection] handle Bind socket_fd={}", socket_fd);

                    {
                        let network_manager_mut = network_manager.borrow_mut();
                        match local_endpoint.addr {
                            Some(address) => {
                                // Bind a properly interface when we have address
                                network_manager_mut.bind_smoltcp_interface(socket_fd, address)
                            }
                            None => {
                                // Bind to default interface when we do not have address, bind to 0.0.0.0 is not support now
                                network_manager_mut.bind_defualt_smoltcp_interface(socket_fd)
                            }
                        }
                    }

                    Connection::with_posix_socket(
                        network_manager.clone(),
                        socket_fd,
                        ipc_reply.clone(),
                        |posix_socket| {
                            let mut posix_socket = posix_socket.borrow_mut();
                            Some(posix_socket.bind(local_endpoint))
                        },
                    );
                }
            }
        }
        true
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        // Release local port
        if let Some(local_port) = *self.local_endpoint.lock() {
            let _ = PORT_GENERATOR.release_port(self.socket_type, local_port.port);
        }
    }
}

// MPSC Queue from heapless requires CAS atomic instructions which are not available on all architectures
pub static NETSTACK_QUEUE: heapless::mpmc::MpMcQueue<Operation, 32> =
    heapless::mpmc::MpMcQueue::<Operation, 32>::new();

// for socket operation
pub type OperationResult = Result<usize, SocketError>;

const IPC_REPLY_TIMEOUT: usize = 1_000;

const STATE_IDLE: usize = 0;
const STATE_WAITING_FOR_CONSUME: usize = 1;
const STATE_AFTER_CONSUME: usize = 2;

pub struct OperationIPCReply {
    reply_result: Mutex<Option<OperationResult>>,
    reply_futex: AtomicUsize,
}

impl OperationIPCReply {
    pub fn new() -> Self {
        Self {
            reply_result: Mutex::new(None),
            reply_futex: AtomicUsize::new(STATE_IDLE),
        }
    }

    fn queue_and_wait(&self, task: Operation) -> ConnectionResult {
        // Must store before enqueue, our connection suppose to be only one thread can write at one time
        while self.reply_futex.load(Ordering::Acquire) != STATE_IDLE {
            yield_me();
        }
        self.reply_futex
            .store(STATE_WAITING_FOR_CONSUME, Ordering::Release);

        // Enqueue creation request to network loop
        NETSTACK_QUEUE.enqueue(task).map_err(|_| {
            // TODO when queue is full , return POSIX EAGAIN error
            //      user can retry in some calls like send/recv, but not for connect / bind which has state change
            self.reply_futex.store(STATE_IDLE, Ordering::Release);
            log::error!("NetStackQueueFull");

            ConnectionError::NetStackQueueFull
        })?;

        self.queue_and_wait_timeout(IPC_REPLY_TIMEOUT)
    }

    fn queue_and_wait_timeout(&self, timeout: usize) -> ConnectionResult {
        let t = scheduler::current_thread();
        log::debug!(
            "[Thread ID 0x{:x}] futex::atomic_wait for addr=0x{:x} begin!",
            Thread::id(&t),
            (self.reply_futex.as_ptr() as *const _ as usize)
        );

        // wait for consume
        if self.reply_futex.load(Ordering::Acquire) == STATE_WAITING_FOR_CONSUME {
            // TODO add timeout
            if let Err(e) = futex::atomic_wait(&self.reply_futex, STATE_WAITING_FOR_CONSUME, None) {
                match e {
                    code::EAGAIN => {
                        // task finish before wait , don't need to wait anymore, continue
                        log::error!("Unknown error from EAGAIN");
                    }
                    code::ETIMEDOUT => {
                        // TODO futex wait timeout
                        log::error!("Unknown error from ETIMEDOUT");
                    }
                    _ => {
                        log::error!("Unknown error from futex::atomic_wait");
                        // unknown state, user may try again , restore state
                        self.reply_futex.store(STATE_IDLE, Ordering::Release);
                        return Err(ConnectionError::PosixError(code::EINTR));
                    }
                }
            }
        }

        log::debug!(
            "[Thread ID 0x{:x}] futex::atomic_wait for addr=0x{:x} finish!",
            Thread::id(&t),
            (self.reply_futex.as_ptr() as *const _ as usize)
        );

        match self.reply_result.lock().take() {
            Some(result) => result.map_err(Into::into),
            None => Err(ConnectionError::Timeout(timeout)),
        }
    }

    fn do_wakeup_client(&self, result: OperationResult) {
        self.reply_result.lock().replace(result);

        // State
        self.reply_futex
            .store(STATE_AFTER_CONSUME, Ordering::Release);

        let _ = futex::atomic_wake(&self.reply_futex, 1);

        self.reply_futex.store(STATE_IDLE, Ordering::Release);
    }

    fn wakeup_client(&self, result: OperationResult, socket_fd: SocketFd) {
        let t = scheduler::current_thread();
        log::debug!(
            "[Thread ID 0x{:x}] futex::atomic_wake fd={} for addr=0x{:x} before emit!",
            Thread::id(&t),
            socket_fd,
            (self.reply_futex.as_ptr() as *const _ as usize)
        );

        self.do_wakeup_client(result);

        log::debug!(
            "[Thread ID 0x{:x}] futex::atomic_wake fd={} for addr=0x{:x} after emit!",
            Thread::id(&t),
            socket_fd,
            (self.reply_futex.as_ptr() as *const _ as usize)
        );
    }
}

pub enum Operation {
    Create {
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
        socket_type: SocketType,
        socket_protocol: SocketProtocol,
        ipc_reply: Arc<OperationIPCReply>,
    },
    Listen {
        socket_fd: SocketFd,
        local_endpoint: IpListenEndpoint,
        ipc_reply: Arc<OperationIPCReply>,
    },

    Connect {
        socket_fd: SocketFd,
        remote_endpoint: IpEndpoint,
        local_port: u16,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },

    Shutdown {
        socket_fd: SocketFd,
        ipc_reply: Arc<OperationIPCReply>,
    },

    /// Send data
    /// only support for connection-mode socket like tcp now
    Send {
        socket_fd: SocketFd,
        f: FnSend,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },

    /// Send data to address
    /// only support for connectionless-mode socket like udp now
    SendTo {
        socket_fd: SocketFd,
        remote_endpoint: IpEndpoint,
        local_port: Option<u16>,
        buffer: &'static [u8],
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },
    SendMsg {
        socket_fd: SocketFd,
        remote_endpoint: IpEndpoint,
        identifer: Option<u16>,
        packet_len: usize,
        f: FnSendMsg,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },
    Recv {
        socket_fd: SocketFd,
        f: FnRecv,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },
    RecvFrom {
        socket_fd: SocketFd,
        f: FnRecvWithEndpoint,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },

    RecvMsg {
        socket_fd: SocketFd,
        f: FnRecvWithEndpoint,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    },

    Bind {
        socket_fd: SocketFd,
        local_endpoint: IpListenEndpoint,
        ipc_reply: Arc<OperationIPCReply>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_connection_creation() {
        let ipc_reply = Arc::new(OperationIPCReply::new());
        let connection = Connection::new(
            1,
            SocketDomain::AfInet,
            SocketType::SockStream,
            SocketProtocol::Tcp,
        );

        assert_eq!(connection.socket_fd, 1);
        assert_eq!(connection.socket_domain, SocketDomain::AfInet);
        assert_eq!(connection.socket_type, SocketType::SockStream);
        assert_eq!(connection.socket_protocol, SocketProtocol::Tcp);
        assert!(connection.local_endpoint.lock().is_none());
        assert!(connection.remote_endpoint.lock().is_none());
    }
    // in test thread, ENQUEUE is not supported, so we cannot test bind now
    // #[test]
    fn test_connection_bind() {
        let ipc_reply = Arc::new(OperationIPCReply::new());
        let connection = Connection::new(
            1,
            SocketDomain::AfInet,
            SocketType::SockStream,
            SocketProtocol::Tcp,
        );

        let local_endpoint = IpEndpoint {
            addr: IpAddress::v4(192, 168, 1, 1),
            port: 8080,
        };

        let result = connection.bind(local_endpoint);
        assert!(result.is_ok());
        assert!(connection.local_endpoint.lock().is_some());
    }
    // in test thread, ENQUEUE is not supported, so we cannot test listen now
    // #[test]
    fn test_connection_listen() {
        let ipc_reply = Arc::new(OperationIPCReply::new());
        let connection = Connection::new(
            1,
            SocketDomain::AfInet,
            SocketType::SockStream,
            SocketProtocol::Tcp,
        );
        let local_endpoint = IpEndpoint {
            addr: IpAddress::v4(192, 168, 1, 1),
            port: 8080,
        };
        let bind_result = connection.bind(local_endpoint);
        assert!(bind_result.is_ok());
        let listen_result = connection.listen();
        assert!(listen_result.is_ok(), "Listen should succeed after binding");
    }
}
