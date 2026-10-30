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

//! Link layer types for the layered network architecture.
//!
//! This module defines the `LinkKind` enum classifying link-layer device types.
//! It is used by the `LinkLayer` trait to describe the kind of physical or
//! virtual link without needing to downcast to the concrete device type.

use core::fmt;

/// Classification of a link-layer device.
///
/// This is a lightweight enum (no data fields) that describes the *kind* of
/// link. For device-specific operations (e.g., WiFi scan), downcast from
/// `dyn LinkLayer` to a device-specific trait like `WifiOps`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkKind {
    /// Loopback device (lo)
    Loopback,
    /// VirtIO network device (virtio-net)
    Virtio,
    /// WiFi (802.11) device
    Wifi,
    /// Ethernet (802.3) device
    Ethernet,
    /// IEEE 802.15.4 device
    Ieee802154,
    /// Unknown or generic device
    Unknown,
}

impl fmt::Display for LinkKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinkKind::Loopback => write!(f, "Loopback"),
            LinkKind::Virtio => write!(f, "Virtio"),
            LinkKind::Wifi => write!(f, "WiFi"),
            LinkKind::Ethernet => write!(f, "Ethernet"),
            LinkKind::Ieee802154 => write!(f, "IEEE802154"),
            LinkKind::Unknown => write!(f, "Unknown"),
        }
    }
}
