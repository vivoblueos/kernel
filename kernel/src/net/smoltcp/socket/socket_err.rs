// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! smoltcp SocketError From impls.

use crate::net::socket::socket_err::SocketError;

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
