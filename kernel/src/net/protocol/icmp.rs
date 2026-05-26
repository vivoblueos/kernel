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

//! ICMP/ICMPv6 protocol implementation.

use alloc::{rc::Rc, string::String};
use core::cell::RefCell;

use crate::net::{
    protocol::{iana, Protocol},
    socket::{icmp::IcmpSocket, socket_err::SocketError, PosixSocket},
    types::{SocketDomain, SocketFd, SocketType},
};

/// ICMP protocol (IANA protocol number 1).
///
/// Handles both ICMPv4 (proto=1) and ICMPv6 (proto=58) via the same
/// `IcmpSocket` implementation.
pub struct IcmpProtocol;

impl Protocol for IcmpProtocol {
    fn protocol_number(&self) -> u8 {
        iana::ICMP
    }

    fn name(&self) -> String {
        String::from("ICMP")
    }

    fn socket_type(&self) -> SocketType {
        SocketType::SockRaw
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
