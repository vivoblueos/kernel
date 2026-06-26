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

use alloc::{collections::btree_map::BTreeMap, rc::Rc, string::String, sync::Arc};
use core::cell::RefCell;

use spin::RwLock;

use crate::net::{
    connection::{OperationIPCReply, OperationResult},
    net_manager::NetworkManager,
    smoltcp::socket::{icmp::IcmpSocket, tcp::TcpSocket, udp::UdpSocket},
    socket::{socket_err::SocketError, PosixSocket},
    types::{SocketDomain, SocketFd, SocketResult, SocketType},
    NetError,
};

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
        network_manager: Rc<RefCell<NetworkManager>>,
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
            return Err(NetError::ProtocolAlreadyRegistered(
                protocol.protocol_number(),
            ));
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
    pub fn get_by_proto(&self, protocol_number: u8) -> Option<Arc<dyn Protocol>> {
        self.by_proto.read().get(&protocol_number).cloned()
    }

    /// Return the number of registered protocols.
    pub fn len(&self) -> usize {
        self.by_key.read().len()
    }

    /// Register an additional `(SocketType, protocol_number)` key pointing to
    /// an already-registered protocol. Useful when one protocol implementation
    /// handles multiple protocol numbers (e.g., ICMPv6 shares IcmpProtocol).
    pub fn register_secondary_key(
        &self,
        protocol: Arc<dyn Protocol>,
        socket_type: SocketType,
        protocol_number: u8,
    ) -> Result<(), NetError> {
        let key = (socket_type, protocol_number);
        let mut by_key = self.by_key.write();
        if by_key.contains_key(&key) {
            return Err(NetError::ProtocolAlreadyRegistered(protocol_number));
        }
        by_key.insert(key, protocol);
        Ok(())
    }

    /// Check whether a `(SocketType, protocol_number)` pair is registered.
    pub fn contains_key(&self, socket_type: SocketType, protocol_number: u8) -> bool {
        self.by_key
            .read()
            .contains_key(&(socket_type, protocol_number))
    }
}

/// Global protocol registry instance.
pub(crate) static PROTOCOL_REGISTRY: ProtocolRegistry = ProtocolRegistry::new();

/// Factory struct for TCP sockets.
struct TcpSocketFactory;

impl Protocol for TcpSocketFactory {
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

/// Factory struct for UDP sockets.
struct UdpSocketFactory;

impl Protocol for UdpSocketFactory {
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
            network_manager,
            socket_fd,
            socket_domain,
        ))))
    }
}

/// Factory struct for ICMP sockets.
struct IcmpSocketFactory;

impl Protocol for IcmpSocketFactory {
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
        socket_fd: SocketFd,
        _socket_domain: SocketDomain,
        network_manager: Rc<RefCell<NetworkManager>>,
    ) -> Result<Rc<RefCell<dyn PosixSocket>>, SocketError> {
        Ok(Rc::new(RefCell::new(IcmpSocket::new(
            network_manager,
            socket_fd,
        ))))
    }
}

/// Initialize and register all built-in protocols.
pub(crate) fn init() {
    let protocols: [Arc<dyn Protocol>; 3] = [
        Arc::new(TcpSocketFactory),
        Arc::new(UdpSocketFactory),
        Arc::new(IcmpSocketFactory),
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

    // Register ICMPv6 as secondary key for IcmpProtocol
    if let Some(icmp) = PROTOCOL_REGISTRY.get_by_key(SocketType::SockRaw, iana::ICMP) {
        let _ = PROTOCOL_REGISTRY.register_secondary_key(icmp, SocketType::SockRaw, iana::ICMPV6);
    }
}
