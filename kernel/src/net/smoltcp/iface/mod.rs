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
//! as a supertrait. Concrete types implement both traits separately,
//! and each `LinkLayer` impl handles the smoltcp poll cycle via
//! `poll_smoltcp()`. `NetIface` stores `Arc<RwLock<dyn LinkLayer>>`
//! (which IS dyn-compatible) for both control operations and smoltcp
//! poll dispatch.

pub(crate) use crate::net::iface::control::{InterfaceFlags, NetIfaceControl, NetIfaceError, NetIfaceResult};
use alloc::{rc::Rc, string::String, sync::Arc, vec::Vec};
use core::cell::RefCell;
use smoltcp::{
    iface::{Interface, SocketHandle, SocketSet},
    socket::AnySocket,
    time::Instant,
};
use spin::RwLock;

use crate::net::link::{HwAddr, LinkLayer, Medium};
use crate::net::smoltcp::link::SmoltcpDevice;
use crate::net::socket::socket_err::SocketError;

/// L3 network interface.
///
/// Bridges the link layer (L2) with the protocol layer (L4).
/// Owns smoltcp Interface and SocketSet directly. Poll dispatch
/// goes through `LinkLayer::poll_smoltcp()` which uses the concrete
/// device type internally.
pub struct NetIface {
    name: String,
    /// Link-layer device for control (L2 operations).
    link: Arc<RwLock<dyn LinkLayer>>,
    /// smoltcp protocol stack operations (separate from L2 control).
    smoltcp: Arc<RwLock<dyn SmoltcpDevice>>,
    /// smoltcp interface.
    smoltcp_iface: Rc<RefCell<Option<Interface>>>,
    /// smoltcp socket set.
    smoltcp_sockets: Rc<RefCell<Option<SocketSet<'static>>>>,
    /// Index into `LINK_REGISTRY`.
    link_index: usize,
}

impl NetIface {
    pub(crate) fn new(
        name: String,
        link: Arc<RwLock<dyn LinkLayer>>,
        smoltcp: Arc<RwLock<dyn SmoltcpDevice>>,
        link_index: usize,
    ) -> Self {
        let (iface, sockets) = smoltcp.write().create_smoltcp_iface();

        NetIface {
            name,
            link,
            smoltcp,
            smoltcp_iface: Rc::new(RefCell::new(Some(iface))),
            smoltcp_sockets: Rc::new(RefCell::new(Some(sockets))),
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
        let sockets = sockets.as_mut().ok_or(SocketError::InterfaceNoAvailable)?;
        let socket = sockets.get_mut::<T>(handle);
        let mut iface = self.smoltcp_iface.borrow_mut();
        let iface = iface.as_mut().ok_or(SocketError::InterfaceNoAvailable)?;
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
            iface
                .ip_addrs()
                .iter()
                .any(|cidr| cidr.contains_addr(&addr))
        } else {
            false
        }
    }

    /// Poll the smoltcp interface for packet I/O.
    ///
    /// Dispatches to `SmoltcpDevice::poll_smoltcp()` which uses the concrete
    /// device type internally, keeping the L2 `LinkLayer` trait smoltcp-free.
    pub fn poll(&self, timestamp: Instant) {
        let mut iface_guard = self.smoltcp_iface.borrow_mut();
        let mut sockets_guard = self.smoltcp_sockets.borrow_mut();
        if let (Some(ref mut iface), Some(ref mut sockets)) =
            (iface_guard.as_mut(), sockets_guard.as_mut())
        {
            let mut smoltcp = self.smoltcp.write();
            smoltcp.poll_smoltcp(timestamp, iface, sockets);

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
    ///
    /// `poll_delay` does not need the device (only `iface.poll_delay` is
    /// called), so it is handled directly without going through LinkLayer.
    pub fn poll_delay(&self, timestamp: Instant) -> Option<smoltcp::time::Duration> {
        let mut iface_guard = self.smoltcp_iface.borrow_mut();
        let sockets_guard = self.smoltcp_sockets.borrow();
        if let (Some(iface), Some(sockets)) = (iface_guard.as_mut(), sockets_guard.as_ref()) {
            iface.poll_delay(timestamp, sockets)
        } else {
            None
        }
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
            NetIfaceControl::SetMacAddress(_mac) => Err(NetIfaceError::NotSupported),
            NetIfaceControl::GetMtu => {
                let link = self.link.read();
                Ok(NetIfaceResult::Mtu(link.mtu()))
            }
            NetIfaceControl::SetMtu(_mtu) => Err(NetIfaceError::NotSupported),
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
                if let Some(ref mut iface) = *self.smoltcp_iface.borrow_mut() {
                    iface.update_ip_addrs(|addrs| {
                        addrs.push(cidr);
                    });
                }
                Ok(NetIfaceResult::Void)
            }
            NetIfaceControl::RemoveAddress(_cidr) => Err(NetIfaceError::NotSupported),
            NetIfaceControl::SetGateway(_gw) => Err(NetIfaceError::NotSupported),
        }
    }
}

impl core::fmt::Display for NetIface {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "NetIface({})", self.name)
    }
}