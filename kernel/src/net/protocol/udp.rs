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

use alloc::rc::Rc;
use alloc::string::String;
use core::cell::RefCell;

use crate::net::protocol::{Protocol, iana};
use crate::net::socket::socket_err::SocketError;
use crate::net::socket::udp::UdpSocket;
use crate::net::socket::PosixSocket;
use crate::net::types::{SocketDomain, SocketFd, SocketType};

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
        _socket_fd: SocketFd,
        _socket_domain: SocketDomain,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError> {
        // Phase 0: see tcp.rs — protocol-based dispatch deferred to Phase 1.
        Err(SocketError::UnsupportedOperation)
    }
}