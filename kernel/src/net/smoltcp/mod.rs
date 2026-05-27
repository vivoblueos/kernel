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

//! smoltcp-specific implementations for the layered network architecture.
//!
//! This module contains all code that directly depends on smoltcp types:
//! NetIface, NetworkManager, TCP/UDP/ICMP sockets, smoltcp link device
//! implementations, and the SmoltcpDevice trait.
//!
//! The abstract traits (LinkLayer, PosixSocket, Protocol, ProtocolRegistry)
//! and non-smoltcp types remain in the parent `net` module.

pub(crate) mod iface;
pub(crate) mod link;
pub(crate) mod socket;