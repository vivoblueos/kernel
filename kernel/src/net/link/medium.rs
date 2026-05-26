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

//! Medium types for the link layer.
//!
//! Mirrors `smoltcp::phy::Medium` to avoid direct smoltcp dependency at the
//! `LinkLayer` trait boundary. Convert to/from smoltcp in the compat layer.

/// The medium type of a link-layer device.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Medium {
    /// Ethernet (IEEE 802.3)
    Ethernet,
    /// IP (no L2 header, e.g., loopback/tun)
    Ip,
    /// IEEE 802.15.4
    Ieee802154,
}

impl From<Medium> for smoltcp::phy::Medium {
    fn from(m: Medium) -> Self {
        match m {
            Medium::Ethernet => smoltcp::phy::Medium::Ethernet,
            Medium::Ip => smoltcp::phy::Medium::Ip,
            Medium::Ieee802154 => smoltcp::phy::Medium::Ieee802154,
        }
    }
}

impl From<smoltcp::phy::Medium> for Medium {
    fn from(m: smoltcp::phy::Medium) -> Self {
        match m {
            smoltcp::phy::Medium::Ethernet => Medium::Ethernet,
            smoltcp::phy::Medium::Ip => Medium::Ip,
            smoltcp::phy::Medium::Ieee802154 => Medium::Ieee802154,
        }
    }
}
