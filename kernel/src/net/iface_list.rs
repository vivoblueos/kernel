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

//! Global NetIface list.
//!
//! Replaces the `net_ifaces` and `default_net_iface` fields previously held
//! inside `NetworkManager`. All NetIface instances are registered here at
//! init time and can be iterated / looked up by any component without
//! borrowing the NetworkManager.

use alloc::{sync::Arc, vec::Vec};
use spin::RwLock;

use crate::net::{
    link::{LinkLayer, LINK_REGISTRY},
    smoltcp::iface::NetIface,
};

/// Global list of network interfaces.
static NET_IFACE_LIST: RwLock<Vec<Arc<NetIface>>> = RwLock::new(Vec::new());

/// Default interface (the last registered non-loopback interface, or loopback).
static DEFAULT_IFACE: RwLock<Option<Arc<NetIface>>> = RwLock::new(None);

/// Register a NetIface and its corresponding LinkLayer into the global registries.
///
/// This is the **single entry point** for all interface+link registration.
/// Both `NET_IFACE_LIST` and `LINK_REGISTRY` are updated atomically (per call).
/// The caller *must* already have populated `LINK_REGISTRY` via `LINK_REGISTRY.init()`
/// before calling this function for the first time.
///
/// If `set_default` is true, this interface becomes the default.
pub fn register(iface: Arc<NetIface>, link: Arc<spin::RwLock<dyn LinkLayer>>, set_default: bool) {
    NET_IFACE_LIST.write().push(iface.clone());
    LINK_REGISTRY.push(link);
    if set_default {
        DEFAULT_IFACE.write().replace(iface);
    }
}

/// Iterate over all registered interfaces (snapshot).
pub fn iter() -> Vec<Arc<NetIface>> {
    NET_IFACE_LIST.read().clone()
}

/// Look up an interface by predicate.
pub fn find<F: FnMut(&Arc<NetIface>) -> bool>(mut f: F) -> Option<Arc<NetIface>> {
    NET_IFACE_LIST.read().iter().find(|&x| f(x)).cloned()
}

/// Get the default interface.
pub fn default() -> Option<Arc<NetIface>> {
    DEFAULT_IFACE.read().clone()
}

/// Set the default interface.
pub fn set_default(iface: Arc<NetIface>) {
    DEFAULT_IFACE.write().replace(iface);
}

/// Number of registered interfaces.
pub fn len() -> usize {
    NET_IFACE_LIST.read().len()
}

/// Check whether the list is empty.
pub fn is_empty() -> bool {
    NET_IFACE_LIST.read().is_empty()
}
