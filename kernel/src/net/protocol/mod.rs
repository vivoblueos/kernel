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

//! Protocol layer (L4) module for the layered network architecture.
//!
//! Defines `Protocol` trait and `ProtocolRegistry` for dynamic protocol
//! registration, replacing the hardcoded `match` in `create_posix_socket`.

use alloc::collections::btree_map::BTreeMap;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::sync::Arc;
use core::cell::RefCell;

use spin::RwLock;

use crate::net::connection::{OperationIPCReply, OperationResult};
use crate::net::socket::socket_err::SocketError;
use crate::net::socket::PosixSocket;
use crate::net::types::{SocketDomain, SocketFd, SocketResult, SocketType};
use crate::net::NetError;

pub(crate) mod icmp;
pub(crate) mod tcp;
pub(crate) mod udp;

/// IANA protocol numbers.
pub mod iana {
    pub const ICMP: u8 = 1;
    pub const TCP: u8 = 6;
    pub const UDP: u8 = 17;
    pub const ICMPV6: u8 = 58;
}

/// L4 protocol trait.
///
/// Each protocol implementation (TCP, UDP, ICMP) registers itself with
/// the `ProtocolRegistry`. During Phase 0, `create_socket` delegates to
/// the existing smoltcp-based socket creation.
pub trait Protocol: Send + Sync + 'static {
    /// IANA protocol number (e.g., 6 for TCP, 17 for UDP, 1 for ICMP).
    fn protocol_number(&self) -> u8;

    /// Human-readable protocol name.
    fn name(&self) -> String;

    /// The socket type used by this protocol.
    fn socket_type(&self) -> SocketType;

    /// Create a new posix socket for this protocol.
    fn create_socket(
        &self,
        socket_fd: SocketFd,
        socket_domain: SocketDomain,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError>;
}

/// Registry of L4 protocols, keyed by `(SocketType, protocol_number)` and
/// by `protocol_number` alone.
pub struct ProtocolRegistry {
    /// Primary key: (SocketType, u8) → Arc<dyn Protocol>
    by_key: RwLock<BTreeMap<(SocketType, u8), Arc<dyn Protocol>>>,
    /// Secondary key: u8 → Arc<dyn Protocol> (for L4 packet dispatch)
    by_proto: RwLock<BTreeMap<u8, Arc<dyn Protocol>>>,
}

impl ProtocolRegistry {
    pub const fn new() -> Self {
        ProtocolRegistry {
            by_key: RwLock::new(BTreeMap::new()),
            by_proto: RwLock::new(BTreeMap::new()),
        }
    }

    /// Register a protocol.
    pub fn register(&self, protocol: Arc<dyn Protocol>) -> Result<(), NetError> {
        let key = (protocol.socket_type(), protocol.protocol_number());
        let mut by_key = self.by_key.write();
        if by_key.contains_key(&key) {
            return Err(NetError::ProtocolAlreadyRegistered(protocol.protocol_number()));
        }
        by_key.insert(key, protocol.clone());

        let mut by_proto = self.by_proto.write();
        by_proto.insert(protocol.protocol_number(), protocol);
        Ok(())
    }

    /// Look up a protocol by `(SocketType, protocol_number)`.
    pub fn get_by_key(
        &self,
        socket_type: SocketType,
        protocol_number: u8,
    ) -> Option<Arc<dyn Protocol>> {
        self.by_key
            .read()
            .get(&(socket_type, protocol_number))
            .cloned()
    }

    /// Look up a protocol by IANA protocol number.
    #[allow(dead_code)]
    pub fn get_by_proto(&self, protocol_number: u8) -> Option<Arc<dyn Protocol>> {
        self.by_proto.read().get(&protocol_number).cloned()
    }

    /// Return the number of registered protocols.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.by_key.read().len()
    }
}

/// Global protocol registry instance.
pub(crate) static PROTOCOL_REGISTRY: ProtocolRegistry = ProtocolRegistry::new();

/// Initialize and register all built-in protocols.
pub(crate) fn init() {
    let protocols: [Arc<dyn Protocol>; 3] = [
        Arc::new(tcp::TcpProtocol),
        Arc::new(udp::UdpProtocol),
        Arc::new(icmp::IcmpProtocol),
    ];

    for proto in protocols {
        let name = proto.name();
        if let Err(e) = PROTOCOL_REGISTRY.register(proto) {
            log::error!("Failed to register protocol {}: {:?}", name, e);
        }
    }
    log::debug!(
        "[ProtocolRegistry] initialized with {} protocols",
        PROTOCOL_REGISTRY.len()
    );
}