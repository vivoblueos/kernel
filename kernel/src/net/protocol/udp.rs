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

//! UDP protocol implementation.

use alloc::{rc::Rc, string::String};
use core::cell::RefCell;

use crate::net::{
    net_manager::NetworkManager,
    protocol::{iana, Protocol},
    socket::{socket_err::SocketError, udp::UdpSocket, PosixSocket},
    types::{SocketDomain, SocketFd, SocketType},
};

/// UDP protocol (IANA protocol number 17).
pub struct UdpProtocol;

impl Protocol for UdpProtocol {
    fn protocol_number(&self) -> u8 {
        iana::UDP
    }

    fn name(&self) -> String {
        String::from("UDP")
    }

    fn socket_type(&self) -> SocketType {
        SocketType::SockDgram
    }

    fn create_socket(
        &self,
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
        network_manager: Rc<RefCell<NetworkManager>>,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError> {
        Ok(Rc::new(RefCell::new(UdpSocket::new(
            network_manager, socket_fd, socket_domain,
        ))))
    }
}
