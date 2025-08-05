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

//! socket_err.rs
use crate::net::{SocketFd, SocketType};
use alloc::string::String;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SocketError {
    #[error("Try again")]
    TryAgain,

    #[error("Operation needs to block to complete")]
    WouldBlock,

    #[error("Posix err {0} , {1}")]
    PosixError(i32, String),

    #[error("Find no posix socket for socket fd {0}")]
    InvalidSocketFd(SocketFd),

    #[error("Invalid smoltcp socket handle")]
    InvalidHandle,

    #[error("Invalid socket state error: {0}")]
    InvalidState(String),

    #[error("Smoltcp interface no available")]
    InterfaceNoAvailable,

    #[error("unsupport socket type {0} for operation {1}")]
    UnsupportedSocketTypeForOperation(SocketType, String),

    #[error("Unsupport socket domain {0}")]
    UnsupportedSocketDomain(i32),

    #[error("Unsupport socket type {0}")]
    UnsupportedSocketType(i32),

    #[error("Unsupport socket protocol {0}")]
    UnsupportedSocketProtocol(i32),

    #[error("Invalid params : {0} for operation {1}")]
    InvalidParam(String, String),

    #[error("create smoltcp socket fail")]
    CreateSmoltcpSocketFail,

    #[error("smoltcp tcp listen error: {0}")]
    SmoltcpTcpListenError(smoltcp::socket::tcp::ListenError),

    #[error("smoltcp tcp connect error: {0}")]
    SmoltcpTcpConnectError(smoltcp::socket::tcp::ConnectError),

    #[error("smoltcp tcp send error: {0}")]
    SmoltcpTcpSendError(smoltcp::socket::tcp::SendError),

    #[error("smoltcp tcp recv error: {0}")]
    SmoltcpTcpRecvError(smoltcp::socket::tcp::RecvError),

    #[error("smoltcp udp bind error: {0}")]
    SmoltcpUdpBindError(smoltcp::socket::udp::BindError),

    #[error("smoltcp udp send error: {0}")]
    SmoltcpUdpSendError(smoltcp::socket::udp::SendError),

    #[error("smoltcp udp recv error: {0}")]
    SmoltcpUdpRecvError(smoltcp::socket::udp::RecvError),

    #[error("smoltcp icmp bind error: {0}")]
    SmoltcpIcmpBindError(smoltcp::socket::icmp::BindError),

    #[error("smoltcp icmp send error: {0}")]
    SmoltcpIcmpSendError(smoltcp::socket::icmp::SendError),

    #[error("smoltcp icmp recv error: {0}")]
    SmoltcpIcmpRecvError(smoltcp::socket::icmp::RecvError),
}

impl From<smoltcp::socket::tcp::ListenError> for SocketError {
    fn from(err: smoltcp::socket::tcp::ListenError) -> Self {
        Self::SmoltcpTcpListenError(err)
    }
}

impl From<smoltcp::socket::tcp::ConnectError> for SocketError {
    fn from(err: smoltcp::socket::tcp::ConnectError) -> Self {
        Self::SmoltcpTcpConnectError(err)
    }
}

impl From<smoltcp::socket::tcp::SendError> for SocketError {
    fn from(err: smoltcp::socket::tcp::SendError) -> Self {
        Self::SmoltcpTcpSendError(err)
    }
}

impl From<smoltcp::socket::tcp::RecvError> for SocketError {
    fn from(err: smoltcp::socket::tcp::RecvError) -> Self {
        Self::SmoltcpTcpRecvError(err)
    }
}

impl From<smoltcp::socket::udp::BindError> for SocketError {
    fn from(err: smoltcp::socket::udp::BindError) -> Self {
        Self::SmoltcpUdpBindError(err)
    }
}

impl From<smoltcp::socket::udp::SendError> for SocketError {
    fn from(err: smoltcp::socket::udp::SendError) -> Self {
        Self::SmoltcpUdpSendError(err)
    }
}

impl From<smoltcp::socket::udp::RecvError> for SocketError {
    fn from(err: smoltcp::socket::udp::RecvError) -> Self {
        Self::SmoltcpUdpRecvError(err)
    }
}

impl From<smoltcp::socket::icmp::BindError> for SocketError {
    fn from(err: smoltcp::socket::icmp::BindError) -> Self {
        Self::SmoltcpIcmpBindError(err)
    }
}

impl From<smoltcp::socket::icmp::SendError> for SocketError {
    fn from(err: smoltcp::socket::icmp::SendError) -> Self {
        Self::SmoltcpIcmpSendError(err)
    }
}

impl From<smoltcp::socket::icmp::RecvError> for SocketError {
    fn from(err: smoltcp::socket::icmp::RecvError) -> Self {
        Self::SmoltcpIcmpRecvError(err)
    }
}
