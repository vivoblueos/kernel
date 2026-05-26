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
//! `LinkLayer` replaces the old `NetDevice` enum. It intentionally does
//! NOT include `smoltcp::phy::Device` as a supertrait because `Device`
//! uses GATs (`RxToken`, `TxToken`) and is not dyn-compatible.
//! Concrete link types implement both `Device` and `LinkLayer` separately.
//!
//! `LinkLayer` provides `poll_smoltcp()` and `create_smoltcp_iface()` which
//! let each concrete implementation handle the smoltcp poll cycle using its
//! own concrete device type. This replaces the SmoltcpDevice enum that was
//! removed in Phase 3.
//!
//! # Key design decisions
//!
//! - **No ioctl**: `LinkLayer` does not expose any type-unsafe `ioctl(cmd, arg)`
//!   method. Device-specific operations are accessed via `Any::downcast_ref`.
//! - **Any bound**: `LinkLayer: Any + 'static` enables safe downcasting.
//! - **dyn-compatible**: `LinkLayer` does NOT include `smoltcp::phy::Device`
//!   (which uses GATs), so `Arc<dyn LinkLayer>` is valid.

pub(crate) mod ethernet_ops;
pub(crate) mod link_kind;
pub(crate) mod medium;
pub(crate) mod wifi_ops;

use core::{any::Any, fmt};

use alloc::{string::String, sync::Arc, vec::Vec};
use smoltcp::{
    iface::{Interface, SocketSet},
    time::Instant,
};
use spin::RwLock;

use crate::net::link::loopback::LoopbackLink;

#[cfg(virtio)]
use crate::devices::net::virtio_net_device::net_dev_exist;
#[cfg(virtio)]
use crate::net::link::virtio::VirtioLink;

pub(crate) use self::{link_kind::LinkKind, medium::Medium};

use super::error::NetError;
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

    /// Create a smoltcp Interface and SocketSet for this device.
    ///
    /// Called during `NetIface::new()` to initialize the smoltcp interface
    /// with the correct medium, hardware address, and configuration for this
    /// concrete device type.
    fn create_smoltcp_iface(&mut self) -> (Interface, SocketSet<'static>);

    /// Poll the smoltcp Interface using this device's concrete Device impl.
    ///
    /// Each concrete `LinkLayer` type implements `smoltcp::phy::Device`
    /// privately and calls `iface.poll(timestamp, &mut self.inner, sockets)`
    /// here. This replaces the `SmoltcpDevice` enum dispatch.
    fn poll_smoltcp(&mut self, timestamp: Instant, iface: &mut Interface, sockets: &mut SocketSet);

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
pub struct LinkRegistry {
    devices: RwLock<Vec<Arc<dyn LinkLayer>>>,
}

impl LinkRegistry {
    pub const fn new() -> Self {
        LinkRegistry {
            devices: RwLock::new(Vec::new()),
        }
    }

    pub fn register(&self, device: Arc<dyn LinkLayer>) {
        log::debug!("[LinkRegistry] register device: {}", device.name());
        self.devices.write().push(device);
    }

    pub fn get(&self, index: usize) -> Option<Arc<dyn LinkLayer>> {
        self.devices.read().get(index).cloned()
    }

    pub fn iter(&self) -> Vec<Arc<dyn LinkLayer>> {
        self.devices.read().clone()
    }

    pub fn len(&self) -> usize {
        self.devices.read().len()
    }

    pub fn find_by_name(&self, name: &str) -> Option<Arc<dyn LinkLayer>> {
        self.devices
            .read()
            .iter()
            .find(|d| d.name() == name)
            .cloned()
    }
}

/// Global link registry instance.
pub(crate) static LINK_REGISTRY: LinkRegistry = LinkRegistry::new();

pub(crate) mod loopback;
#[cfg(virtio)]
pub(crate) mod virtio;

/// Initialize and register all built-in link-layer devices.
pub(crate) fn init() {
    let lo = Arc::new(LoopbackLink::new());
    LINK_REGISTRY.register(lo);
    log::debug!("[LinkLayer] registered loopback");

    #[cfg(virtio)]
    if net_dev_exist() {
        let virtio = Arc::new(VirtioLink::new(0));
        LINK_REGISTRY.register(virtio);
        log::debug!("[LinkLayer] registered virtio-net");
    }
}
