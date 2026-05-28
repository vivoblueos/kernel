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

//! Link layer module for the layered network architecture.
//!
//! This module defines the `LinkLayer` trait, `LinkRegistry`, and the
//! `downcast_ref` helper for accessing device-specific traits.
//!
//! `LinkLayer` is the pure L2 abstraction — it has NO dependency on
//! `smoltcp`. Concrete link types implement `LinkLayer` for device
//! control (name, MTU, MAC, etc.) and separately implement
//! `smoltcp::phy::Device` + `SmoltcpDevice` (from `crate::net::smoltcp::link`)
//! for the protocol stack.
//!
//! `NetIface` holds separate `Arc<RwLock<dyn LinkLayer>>` and
//! `Arc<RwLock<dyn SmoltcpDevice>>` references to the same concrete device.
//!
//! # Key design decisions
//!
//! - **No ioctl**: `LinkLayer` does not expose any type-unsafe `ioctl(cmd, arg)`
//!   method. Device-specific operations are accessed via `Any::downcast_ref`.
//! - **Any bound**: `LinkLayer: Any + 'static` enables safe downcasting.
//! - **dyn-compatible**: `LinkLayer` is dyn-compatible.

pub(crate) mod ethernet_ops;
pub(crate) mod link_kind;
pub(crate) mod loopback;
pub(crate) mod medium;
#[cfg(virtio)]
pub(crate) mod virtio;
pub(crate) mod wifi_ops;

use core::{any::Any, fmt};

use alloc::{string::String, sync::Arc, vec::Vec};
use spin;

pub(crate) use self::{link_kind::LinkKind, medium::Medium};

use crate::net::iface::{InterfaceFlags, NetIfaceControl, NetIfaceError, NetIfaceResult};
use crate::net::link::{ethernet_ops::EthernetOps, wifi_ops::WifiOps};

/// A hardware address (MAC or similar).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HwAddr {
    pub bytes: [u8; 8],
    pub len: u8,
}

impl HwAddr {
    pub fn from_ethernet(mac: [u8; 6]) -> Self {
        let mut bytes = [0u8; 8];
        bytes[..6].copy_from_slice(&mac);
        HwAddr { bytes, len: 6 }
    }

    pub fn as_ethernet(&self) -> Option<[u8; 6]> {
        if self.len == 6 {
            let mut mac = [0u8; 6];
            mac.copy_from_slice(&self.bytes[..6]);
            Some(mac)
        } else {
            None
        }
    }
}

impl fmt::Display for HwAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, b) in self.bytes[..self.len as usize].iter().enumerate() {
            if i > 0 {
                write!(f, ":")?;
            }
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

/// Link-layer device trait for the layered network architecture.
///
/// Replaces the old `NetDevice` enum. Concrete link types implement both
/// `smoltcp::phy::Device` (with GATs) and `LinkLayer` separately — `Device`
/// is NOT a supertrait here because GATs make it not dyn-compatible.
///
/// The `Any` bound enables downcasting to concrete types and device-specific
/// operation traits (e.g., `WifiOps`, `EthernetOps`).
pub trait LinkLayer: Send + Sync + Any + 'static {
    /// Human-readable device name (e.g., "lo", "eth0").
    fn name(&self) -> String;
    /// Medium type (Ethernet, Ip, Ieee802154).
    fn medium(&self) -> Medium;
    /// Maximum transmission unit in bytes.
    fn mtu(&self) -> usize;
    /// Hardware address (MAC for Ethernet, None for loopback).
    fn hw_addr(&self) -> Option<HwAddr>;
    /// Kind of link device.
    fn kind(&self) -> LinkKind;
    /// Whether the device can currently send.
    fn can_send(&self) -> bool;
    /// Whether the device can currently receive.
    fn can_recv(&self) -> bool;

    /// Optional: return a reference to this device's `WifiOps` implementation.
    fn as_wifi(&mut self) -> Option<&mut dyn WifiOps> {
        None
    }

    /// Optional: return a reference to this device's `EthernetOps` implementation.
    fn as_ethernet(&mut self) -> Option<&mut dyn EthernetOps> {
        None
    }
}

/// Downcast helper for `dyn LinkLayer`.
impl dyn LinkLayer {
    /// Downcast to a concrete `LinkLayer` implementation.
    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref::<T>()
    }
}

/// Global registry of link-layer devices.
///
/// # Safety
///
/// All devices must be registered during `net::init()`, before the network
/// thread starts. After that, the registry is immutable — no further `register()`
/// calls are allowed. This eliminates locking overhead for reads.
///
/// `init()` panics if called more than once.
pub(crate) struct LinkRegistry {
    devices: spin::Once<Vec<Arc<spin::RwLock<dyn LinkLayer>>>>,
}

impl LinkRegistry {
    pub const fn new() -> Self {
        LinkRegistry {
            devices: spin::Once::new(),
        }
    }

    /// Initialize the registry with all devices. Must be called exactly once
    /// during `net::init()` before the network thread starts.
    pub fn init(&self, devices: Vec<Arc<spin::RwLock<dyn LinkLayer>>>) {
        self.devices.call_once(|| devices);
    }

    pub fn get(&self, index: usize) -> Option<Arc<spin::RwLock<dyn LinkLayer>>> {
        self.devices.get()?.get(index).cloned()
    }

    pub fn iter(&self) -> Vec<Arc<spin::RwLock<dyn LinkLayer>>> {
        self.devices.get().cloned().unwrap_or_default()
    }

    pub fn len(&self) -> usize {
        self.devices.get().map_or(0, Vec::len)
    }

    pub fn find_by_name(&self, name: &str) -> Option<Arc<spin::RwLock<dyn LinkLayer>>> {
        self.devices.get()?.iter().find(|d| d.read().name() == name).cloned()
    }
}

/// Global link registry instance.
pub(crate) static LINK_REGISTRY: LinkRegistry = LinkRegistry::new();

/// Handle a type-safe network control command against the first registered link device.
///
/// Bridges the POSIX ioctl path (via `Operation::NetControl`) to `LinkLayer`
/// queries. Only simple getters (flags, MAC, MTU, link kind) are supported;
/// IP configuration and WiFi operations are dispatched through `NetIface::control()`
/// which has access to the full smoltcp stack.
pub(crate) fn handle_control(cmd: NetIfaceControl) -> Result<NetIfaceResult, NetIfaceError> {
    let link_arc = LINK_REGISTRY.get(0).ok_or(NetIfaceError::DeviceNotFound)?;
    let link = link_arc.read();

    match cmd {
        NetIfaceControl::GetFlags => Ok(NetIfaceResult::Flags(InterfaceFlags {
            up: link.can_send() || link.can_recv(),
            running: true,
            promiscuous: false,
        })),
        NetIfaceControl::GetMacAddress => {
            let hw = link
                .hw_addr()
                .and_then(|h| h.as_ethernet())
                .unwrap_or([0u8; 6]);
            Ok(NetIfaceResult::MacAddress(hw))
        }
        NetIfaceControl::GetMtu => Ok(NetIfaceResult::Mtu(link.mtu())),
        NetIfaceControl::GetLinkKind => Ok(NetIfaceResult::LinkKind(link.kind())),
        _ => Err(NetIfaceError::NotSupported),
    }
}

