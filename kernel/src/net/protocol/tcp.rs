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

use alloc::rc::Rc;
use alloc::string::String;
use core::cell::RefCell;

use crate::net::protocol::{Protocol, iana};
use crate::net::socket::socket_err::SocketError;
use crate::net::socket::tcp::TcpSocket;
use crate::net::socket::PosixSocket;
use crate::net::types::{SocketDomain, SocketFd, SocketType};

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
        _socket_fd: SocketFd,
        _socket_domain: SocketDomain,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError> {
        // Phase 0: Protocol registry is initialized but socket creation
        // still goes through NetworkManager::create_posix_socket().
        // Full protocol-based dispatch will be wired in Phase 1.
        Err(SocketError::UnsupportedOperation)
    }
}