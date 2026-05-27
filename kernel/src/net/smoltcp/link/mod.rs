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

//! smoltcp protocol stack operations trait and helpers.

use core::any::Any;

/// smoltcp protocol stack operations for a link-layer device.
///
/// This trait is **separate** from `LinkLayer`. Each concrete link type
/// implements both — `LinkLayer` for L2 control and `SmoltcpDevice`
/// for smoltcp-specific lifecycle. `NetIface` holds two separate
/// `Arc<RwLock<...>>` references, one for each trait.
///
/// Both methods take `&mut self` so concrete impls can access their
/// `smoltcp::phy::Device` implementation, which is NOT dyn-compatible
/// (GATs on `RxToken`/`TxToken`).
pub trait SmoltcpDevice: Any + 'static {
    /// Create a smoltcp Interface and SocketSet for this device.
    fn create_smoltcp_iface(&mut self) -> (smoltcp::iface::Interface, smoltcp::iface::SocketSet<'static>);

    /// Poll the smoltcp Interface using this device's concrete Device impl.
    fn poll_smoltcp(
        &mut self,
        timestamp: smoltcp::time::Instant,
        iface: &mut smoltcp::iface::Interface,
        sockets: &mut smoltcp::iface::SocketSet,
    );
}

impl dyn SmoltcpDevice {
    /// Downcast to a concrete `SmoltcpDevice` implementation.
    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref::<T>()
    }
}