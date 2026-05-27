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

//! TCP protocol implementation.

use alloc::{rc::Rc, string::String};
use core::cell::RefCell;

use crate::net::{
    net_manager::NetworkManager,
    protocol::{iana, Protocol},
    socket::{socket_err::SocketError, tcp::TcpSocket, PosixSocket},
    types::{SocketDomain, SocketFd, SocketType},
};

/// TCP protocol (IANA protocol number 6).
pub struct TcpProtocol;

impl Protocol for TcpProtocol {
    fn protocol_number(&self) -> u8 {
        iana::TCP
    }

    fn name(&self) -> String {
        String::from("TCP")
    }

    fn socket_type(&self) -> SocketType {
        SocketType::SockStream
    }

    fn create_socket(
        &self,
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
        network_manager: Rc<RefCell<NetworkManager>>,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError> {
        Ok(Rc::new(RefCell::new(TcpSocket::new(
            network_manager,
            socket_fd,
            socket_domain,
        ))))
    }
}
