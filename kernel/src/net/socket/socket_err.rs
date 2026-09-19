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

    #[error("unsupported socket type {0} for operation {1}")]
    UnsupportedSocketTypeForOperation(SocketType, String),

    #[error("Unsupported socket domain {0}")]
    UnsupportedSocketDomain(i32),

    #[error("Unsupported socket type {0}")]
    UnsupportedSocketType(i32),

    #[error("Unsupported socket protocol {0}")]
    UnsupportedSocketProtocol(i32),

    #[error("Unsupported operation")]
    UnsupportedOperation,

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

impl SocketError {
    pub fn to_errno(&self) -> i32 {
        match self {
            Self::TryAgain | Self::WouldBlock => -libc::EAGAIN,
            Self::InvalidSocketFd(_) => -libc::EBADF,
            Self::UnsupportedSocketTypeForOperation(_, _) => -libc::EOPNOTSUPP,
            Self::InvalidState(_) => -libc::EINVAL,
            Self::PosixError(errno, _) => *errno,
            Self::UnsupportedOperation => -libc::ENOSYS,
            Self::InvalidParam(_, _) => -libc::EINVAL,
            _ => -libc::EIO,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn maps_socket_errors_to_negative_errno() {
        assert_eq!(SocketError::WouldBlock.to_errno(), -libc::EAGAIN);
        assert_eq!(SocketError::InvalidSocketFd(3).to_errno(), -libc::EBADF);
        assert_eq!(SocketError::UnsupportedOperation.to_errno(), -libc::ENOSYS);
    }

    #[test]
    fn preserves_explicit_posix_errno() {
        let error = SocketError::PosixError(-libc::ECONNRESET, String::new());
        assert_eq!(error.to_errno(), -libc::ECONNRESET);
    }
}
