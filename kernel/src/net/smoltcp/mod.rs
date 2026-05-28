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

use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::cell::RefCell;
use smoltcp::wire::IpAddress;
use spin;

use crate::net::iface_list;
use crate::net::link::LinkLayer;
use crate::net::link::LINK_REGISTRY;
use crate::net::smoltcp::iface::NetIface;
use crate::net::socket::PosixSocket;
use crate::net::SocketFd;
use crate::net::smoltcp::link::SmoltcpDevice;

/// Entry in the device registration list: (name, set_default, Arc<dyn SmoltcpDevice>).
pub(crate) type DeviceEntry = (&'static str, bool, Arc<spin::RwLock<dyn SmoltcpDevice>>);

/// Initialize the link registry with all devices and register their
/// NetIface instances. Must be called exactly once during `net::init()`
/// before the network thread starts.
///
/// Each entry is `(device, name, set_default)`. Returns the created
/// `NetIface` instances in registration order.
pub(crate) fn init_devices(devices: &[DeviceEntry]) -> Vec<Arc<NetIface>> {
    let link_devices: Vec<Arc<spin::RwLock<dyn LinkLayer>>> =
        devices.iter().map(|(_, _, link)| link.clone() as Arc<spin::RwLock<dyn LinkLayer>>).collect();
    LINK_REGISTRY.init(link_devices);

    let mut ifaces = Vec::new();
    for (i, (name, set_default, _)) in devices.iter().enumerate() {
        let link = devices[i].2.clone();
        let iface = Arc::new(NetIface::new(name.to_string(), link, i));
        iface_list::register(iface.clone(), *set_default);
        ifaces.push(iface);
    }
    ifaces
}

/// Bind a socket to the default NetIface.
pub(crate) fn bind_default_interface(
    socket_fd: SocketFd,
    socket: Rc<RefCell<dyn PosixSocket>>,
) {
    if let Some(interface) = iface_list::default() {
        let mut socket = socket.borrow_mut();
        socket.bind_interface(interface.clone());
        log::debug!("Socket Fd={} binding to {}", socket_fd, interface);
    } else {
        log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
    }
}

/// Bind a socket to the NetIface that contains `binding_addr`,
/// falling back to the default interface.
pub(crate) fn bind_interface_by_addr(
    socket_fd: SocketFd,
    socket: Rc<RefCell<dyn PosixSocket>>,
    binding_addr: IpAddress,
) {
    iface_list::find(|iface| iface.contains_addr(binding_addr))
        .map_or_else(
            || {
                if let Some(interface) = iface_list::default() {
                    let mut socket = socket.borrow_mut();
                    socket.bind_interface(interface.clone());
                    log::debug!("Socket Fd={} binding to {}", socket_fd, interface);
                } else {
                    log::error!("Socket Fd={} binding fail, find no interface", socket_fd);
                }
            },
            |iface| {
                let mut socket = socket.borrow_mut();
                socket.bind_interface(iface.clone());
                log::debug!("Socket Fd={} binding to {}", socket_fd, iface);
            },
        )
}