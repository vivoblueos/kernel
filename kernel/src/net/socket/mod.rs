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

use smoltcp::wire::{IpAddress, IpEndpoint, IpListenEndpoint};

use crate::net::{
    connection::{Operation, OperationIPCReply, OperationResult},
    net_interface::NetInterface,
    socket::socket_err::SocketError,
    SocketResult,
};
use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::{cell::RefCell, net::SocketAddr};

pub mod icmp;
pub mod socket_err;
pub mod socket_waker;
pub mod tcp;
pub mod udp;

pub(crate) type FnSend = Box<dyn FnOnce(&mut [u8]) -> (usize, usize) + Send>;
pub(crate) type FnSendMsg = Box<dyn FnOnce(&mut [u8]) -> usize + Send>;
pub(crate) type FnRecv = Box<dyn FnOnce(&mut [u8]) -> (usize, usize) + Send>;
pub(crate) type FnRecvWithEndpoint = Box<dyn FnOnce(&[u8], IpEndpoint) -> usize + Send>;

pub trait PosixSocket {
    // smoltcp need to bind socket with interface
    fn bind_interface(&mut self, interface: Rc<RefCell<NetInterface<'static>>>);

    fn accept(&self, _local_endpoint: IpListenEndpoint) -> SocketResult;

    fn bind(&mut self, local_endpoint: IpListenEndpoint) -> SocketResult;

    fn connect(
        &mut self,
        remote_endpoint: IpEndpoint,
        local_port: u16,
        is_nonblocking: bool,
    ) -> SocketResult;

    fn listen(&mut self, local_endpoint: IpListenEndpoint) -> SocketResult;

    fn send(
        &mut self,
        f: FnSend,
        flag: i32,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn sendto(
        &mut self,
        message: &'static [u8],
        _flag: i32,
        remote_endpoint: IpEndpoint,
        local_port: Option<u16>,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn sendmsg(
        &mut self,
        remote_endpoint: IpEndpoint,
        identifier: Option<u16>,
        packet_len: usize,
        f: FnSendMsg,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn recv(
        &mut self,
        f: FnRecv,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn recvmsg(
        &mut self,
        f: FnRecvWithEndpoint,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn recvfrom(
        &mut self,
        f: FnRecvWithEndpoint,
        is_nonblocking: bool,
        ipc_reply: Arc<OperationIPCReply>,
    ) -> SocketResult;

    fn getsockname(&mut self, f: Box<dyn FnOnce(IpEndpoint) + Send>) -> SocketResult;

    fn getpeername(&mut self, f: Box<dyn FnOnce(IpEndpoint) + Send>) -> SocketResult;

    fn shutdown(&self) -> SocketResult;

    fn is_shutdown(&self) -> bool;
}
