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

//! Network interface module for the layered architecture.
//!
//! `NetIface` is the L3 abstraction representing a network interface.
//! It owns a reference to a `LinkLayer` device (L2) and provides
//! type-safe control via `NetIfaceControl`.
//!
//! # Dyn-compatibility note
//!
//! `smoltcp::phy::Device` uses GATs (`RxToken`, `TxToken`) and is NOT
//! dyn-compatible. `LinkLayer` intentionally does NOT include `Device`
//! as a supertrait. Concrete types implement both traits separately.
//! `NetIface` stores `Arc<RwLock<dyn LinkLayer>>` (which IS dyn-compatible)
//! for control operations. For smoltcp `poll()`, the `SmoltcpDevice` enum
//! holds the concrete device — this will be removed in Phase 2 when
//! smoltcp is phased out.

pub(crate) mod addr;
pub(crate) mod control;

use alloc::rc::Rc;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::RefCell;
use smoltcp::iface::{Interface, SocketHandle, SocketSet};
use smoltcp::socket::AnySocket;
use smoltcp::time::Instant;
use smoltcp::wire::IpCidr;
use spin::{Mutex, RwLock};

use self::addr::{IpAddrConfig, RouteConfig};
pub(crate) use self::control::{InterfaceFlags, NetIfaceControl, NetIfaceError, NetIfaceResult};
use crate::net::link::{LinkLayer, HwAddr, Medium};
use crate::net::link::loopback::LoopbackLink;
#[cfg(virtio)]
use crate::net::link::virtio::VirtioLink;

use crate::net::socket::socket_err::SocketError;

/// Concrete device wrapper for smoltcp compatibility.
///
/// `smoltcp::phy::Device` uses GATs and is not dyn-compatible. This enum
/// wraps concrete device types. Instead of implementing `Device` (which
/// requires unified GAT type aliases across variants), it provides
/// `poll_with()` and `poll_delay_with()` that match the same pattern as
/// the old `NetInterface::poll()`.
///
/// Removed in Phase 2 when smoltcp is phased out.
pub(crate) enum SmoltcpDevice {
    Loopback(LoopbackLink),
    #[cfg(virtio)]
    Virtio(VirtioLink),
}

impl SmoltcpDevice {
    /// Create smoltcp Interface + SocketSet.
    /// Called during NetIface initialization.
    pub fn create_smoltcp_iface_and_sockets(&mut self) -> Option<(Interface, SocketSet<'static>)> {
        match self {
            SmoltcpDevice::Loopback(ref mut dev) => {
                use smoltcp::iface::Config;
                use smoltcp::phy::Device;
                use smoltcp::wire::{HardwareAddress, IpAddress, IpCidr};

                let caps = dev.capabilities();
                let config = match caps.medium {
                    smoltcp::phy::Medium::Ethernet => Config::new(HardwareAddress::Ethernet(
                        smoltcp::wire::EthernetAddress([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]),
                    )),
                    smoltcp::phy::Medium::Ip => Config::new(HardwareAddress::Ip),
                    smoltcp::phy::Medium::Ieee802154 => todo!(),
                };
                let mut iface = Interface::new(
                    config,
                    dev,
                    Instant::from_millis(i64::try_from(crate::time::now().as_millis()).unwrap_or(0)),
                );
                if caps.medium == smoltcp::phy::Medium::Ip {
                    iface.update_ip_addrs(|addrs| {
                        let _ = addrs.push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8));
                        let _ = addrs.push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128));
                    });
                }
                let sockets = SocketSet::new(vec![]);
                Some((iface, sockets))
            }
            #[cfg(virtio)]
            SmoltcpDevice::Virtio(ref mut dev) => {
                use smoltcp::iface::Config;
                use smoltcp::phy::Device;
                use smoltcp::wire::{EthernetAddress, HardwareAddress, IpAddress, IpCidr};

                let caps = dev.capabilities();
                let config = match caps.medium {
                    smoltcp::phy::Medium::Ethernet => {
                        let mac = [0x02, 0x00, 0x00, 0x00, 0x00, 0x01];
                        Config::new(HardwareAddress::Ethernet(EthernetAddress(mac)))
                    }
                    smoltcp::phy::Medium::Ip => Config::new(HardwareAddress::Ip),
                    smoltcp::phy::Medium::Ieee802154 => todo!(),
                };
                let mut iface = Interface::new(
                    config,
                    dev,
                    Instant::from_millis(i64::try_from(crate::time::now().as_millis()).unwrap_or(0)),
                );
                if caps.medium == smoltcp::phy::Medium::Ip {
                    iface.update_ip_addrs(|addrs| {
                        let _ = addrs.push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8));
                        let _ = addrs.push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128));
                    });
                }
                let sockets = SocketSet::new(vec![]);
                Some((iface, sockets))
            }
        }
    }

    /// Poll smoltcp using the concrete device inside this enum.
    fn poll_with(
        &mut self,
        iface: &mut Interface,
        sockets: &mut SocketSet<'_>,
        timestamp: Instant,
    ) {
        match self {
            SmoltcpDevice::Loopback(dev) => {
                iface.poll(timestamp, dev, sockets);
            }
            #[cfg(virtio)]
            SmoltcpDevice::Virtio(dev) => {
                iface.poll(timestamp, dev, sockets);
            }
        }
    }

    /// Get the poll delay using the concrete device inside this enum.
    fn poll_delay_with(
        &self,
        iface: &mut Interface,
        sockets: &SocketSet<'_>,
        timestamp: Instant,
    ) -> Option<smoltcp::time::Duration> {
        match self {
            SmoltcpDevice::Loopback(_) => iface.poll_delay(timestamp, sockets),
            #[cfg(virtio)]
            SmoltcpDevice::Virtio(_) => iface.poll_delay(timestamp, sockets),
        }
    }
}

/// L3 network interface.
///
/// Bridges the link layer (L2) with the protocol layer (L4).
/// Owns smoltcp Interface and SocketSet directly.
pub struct NetIface {
    name: String,
    /// Link-layer device for control operations (dyn-compatible).
    link: Arc<RwLock<dyn LinkLayer>>,
    ip_config: Mutex<IpAddrConfig>,
    routes: Mutex<Vec<RouteConfig>>,
    /// Concrete device for smoltcp poll (not dyn-compatible due to GATs).
    smoltcp_dev: Mutex<SmoltcpDevice>,
    /// smoltcp interface.
    smoltcp_iface: Rc<RefCell<Option<Interface>>>,
    /// smoltcp socket set.
    smoltcp_sockets: Rc<RefCell<Option<SocketSet<'static>>>>,
    /// Index into `LINK_REGISTRY`.
    link_index: usize,
}

impl NetIface {
    pub(crate) fn new(name: String, link: Arc<RwLock<dyn LinkLayer>>, mut smoltcp_device: SmoltcpDevice, link_index: usize) -> Self {
        let (smoltcp_iface, smoltcp_sockets) = smoltcp_device
            .create_smoltcp_iface_and_sockets()
            .map(|(iface, sockets)| (
                Rc::new(RefCell::new(Some(iface))),
                Rc::new(RefCell::new(Some(sockets))),
            ))
            .unwrap_or_else(|| (
                Rc::new(RefCell::new(None)),
                Rc::new(RefCell::new(None)),
            ));

        NetIface {
            name,
            link,
            ip_config: Mutex::new(IpAddrConfig::new()),
            routes: Mutex::new(Vec::new()),
            smoltcp_dev: Mutex::new(smoltcp_device),
            smoltcp_iface,
            smoltcp_sockets,
            link_index,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn link(&self) -> &Arc<RwLock<dyn LinkLayer>> {
        &self.link
    }

    pub fn link_index(&self) -> usize {
        self.link_index
    }

    /// Set the smoltcp interface and socket set (bridge during migration).
    pub fn set_smoltcp(&self, iface: Interface, sockets: SocketSet<'static>) {
        self.smoltcp_iface.replace(Some(iface));
        self.smoltcp_sockets.replace(Some(sockets));
    }

    pub fn smoltcp_iface(&self) -> &Rc<RefCell<Option<Interface>>> {
        &self.smoltcp_iface
    }

    pub fn smoltcp_sockets(&self) -> &Rc<RefCell<Option<SocketSet<'static>>>> {
        &self.smoltcp_sockets
    }

    /// Add a smoltcp socket to this interface's socket set.
    pub fn add_socket<T: AnySocket<'static>>(&self, socket: T) -> Option<SocketHandle> {
        self.smoltcp_sockets
            .borrow_mut()
            .as_mut()
            .map(|sockets| sockets.add(socket))
    }

    /// Execute a closure with a smoltcp socket and Interface reference.
    ///
    /// Similar to the `with()` pattern used in TCP/UDP/ICMP sockets, but
    /// as a method on `NetIface` so sockets don't need to manage the locking.
    pub fn with_socket<T, F, R>(&self, handle: SocketHandle, f: F) -> Result<R, SocketError>
    where
        T: AnySocket<'static>,
        F: FnOnce(&mut T, &mut Interface) -> Result<R, SocketError>,
    {
        let mut sockets = self.smoltcp_sockets.borrow_mut();
        let sockets = sockets
            .as_mut()
            .ok_or(SocketError::InterfaceNoAvailable)?;
        let socket = sockets.get_mut::<T>(handle);
        let mut iface = self.smoltcp_iface.borrow_mut();
        let iface = iface
            .as_mut()
            .ok_or(SocketError::InterfaceNoAvailable)?;
        f(socket, iface)
    }

    /// Remove a socket from this interface's socket set.
    pub fn remove_socket(&self, handle: SocketHandle) {
        if let Some(ref mut sockets) = *self.smoltcp_sockets.borrow_mut() {
            sockets.remove(handle);
        }
    }

    /// Check if the interface contains an IP address.
    pub fn contains_addr(&self, addr: smoltcp::wire::IpAddress) -> bool {
        if let Some(ref iface) = *self.smoltcp_iface.borrow() {
            iface.ip_addrs().iter().any(|cidr| cidr.contains_addr(&addr))
        } else {
            self.ip_config
                .lock()
                .addresses
                .iter()
                .any(|cidr| cidr.contains_addr(&addr))
        }
    }

    /// Poll the smoltcp interface for packet I/O.
    ///
    /// Uses the `SmoltcpDevice` enum (not `dyn LinkLayer`) because
    /// `smoltcp::phy::Device` uses GATs and is not dyn-compatible.
    /// Removed in Phase 2 when smoltcp is phased out.
    pub fn poll(&self, timestamp: Instant) {
        let mut dev = self.smoltcp_dev.lock();
        let mut iface_guard = self.smoltcp_iface.borrow_mut();
        let mut sockets_guard = self.smoltcp_sockets.borrow_mut();
        if let (Some(ref mut iface), Some(ref mut sockets)) =
            (iface_guard.as_mut(), sockets_guard.as_mut())
        {
            dev.poll_with(iface, sockets, timestamp);

            // Phase 1 marker: native RX path placeholder.
            // In Phase 2, after poll(), we will:
            //   1. Read raw L2 frame from the link device
            //   2. Parse L2 header (Ethernet or IP)
            //   3. Create PacketMeta { iface_index, ip_proto }
            //   4. Wrap payload in Packet { meta, buffer, data_start, data_len }
            //   5. Dispatch via PROTOCOL_REGISTRY.get_by_proto(ip_proto)
        }
    }

    /// Poll delay from smoltcp.
    pub fn poll_delay(&self, timestamp: Instant) -> Option<smoltcp::time::Duration> {
        let dev = self.smoltcp_dev.lock();
        let mut iface_guard = self.smoltcp_iface.borrow_mut();
        let mut sockets_guard = self.smoltcp_sockets.borrow_mut();
        if let (Some(iface), Some(sockets)) =
            (iface_guard.as_mut(), sockets_guard.as_mut())
        {
            dev.poll_delay_with(iface, sockets, timestamp)
        } else {
            None
        }
    }

    /// Add an IP address to the interface.
    pub fn add_address(&self, cidr: IpCidr) {
        if let Some(ref mut iface) = *self.smoltcp_iface.borrow_mut() {
            iface.update_ip_addrs(|addrs| { addrs.push(cidr); });
        }
        self.ip_config.lock().addresses.push(cidr);
    }

    /// Type-safe control method.
    ///
    /// Routes control commands to the appropriate handler. Device-specific
    /// operations (e.g., WiFi scan) are dispatched by downcasting from
    /// `dyn LinkLayer` to the device-specific trait.
    pub fn control(&self, cmd: NetIfaceControl) -> Result<NetIfaceResult, NetIfaceError> {
        match cmd {
            NetIfaceControl::GetFlags => {
                let link = self.link.read();
                Ok(NetIfaceResult::Flags(InterfaceFlags {
                    up: link.can_send() || link.can_recv(),
                    running: true,
                    promiscuous: false,
                }))
            }
            NetIfaceControl::SetFlags(_flags) => {
                // TODO: implement flag setting
                Ok(NetIfaceResult::Void)
            }
            NetIfaceControl::GetMacAddress => {
                let link = self.link.read();
                match link.hw_addr() {
                    Some(hw) => Ok(NetIfaceResult::MacAddress(
                        hw.as_ethernet().unwrap_or([0u8; 6]),
                    )),
                    None => Ok(NetIfaceResult::MacAddress([0u8; 6])),
                }
            }
            NetIfaceControl::SetMacAddress(_mac) => {
                Err(NetIfaceError::NotSupported)
            }
            NetIfaceControl::GetMtu => {
                let link = self.link.read();
                Ok(NetIfaceResult::Mtu(link.mtu()))
            }
            NetIfaceControl::SetMtu(_mtu) => {
                Err(NetIfaceError::NotSupported)
            }
            NetIfaceControl::Up | NetIfaceControl::Down => {
                // State tracking — no-op in Phase 0
                Ok(NetIfaceResult::Void)
            }
            NetIfaceControl::GetLinkKind => {
                let link = self.link.read();
                Ok(NetIfaceResult::LinkKind(link.kind()))
            }
            NetIfaceControl::WifiScan => {
                let mut link = self.link.write();
                let wifi = link
                    .as_wifi()
                    .ok_or(NetIfaceError::DeviceTraitNotAvailable)?;
                wifi.scan()
                    .map(NetIfaceResult::WifiScanResult)
                    .map_err(|_| NetIfaceError::DeviceTraitNotAvailable)
            }
            NetIfaceControl::WifiConnect { .. }
            | NetIfaceControl::WifiDisconnect
            | NetIfaceControl::WifiSignalStrength
            | NetIfaceControl::EthernetSetPromiscuous(_) => {
                Err(NetIfaceError::DeviceTraitNotAvailable)
            }
            NetIfaceControl::AddAddress(cidr) => {
                self.add_address(cidr);
                Ok(NetIfaceResult::Void)
            }
            NetIfaceControl::RemoveAddress(_cidr) => {
                Err(NetIfaceError::NotSupported)
            }
            NetIfaceControl::SetGateway(_gw) => {
                Err(NetIfaceError::NotSupported)
            }
        }
    }
}

impl core::fmt::Display for NetIface {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NetIface({})", self.name)
    }
}