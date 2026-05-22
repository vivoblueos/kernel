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

//! VirtIO link-layer device.
//!
//! Wraps `VirtIONetDevice` and implements `LinkLayer`.

use alloc::string::String;

use smoltcp::phy::{Device, DeviceCapabilities, Medium as SmoltcpMedium};
use smoltcp::time::Instant;

use crate::devices::net::virtio_net_device::{
    VirtIONetDevice, VirtIONetRxToken, VirtIONetTxToken,
};
use crate::net::link::{HwAddr, LinkKind, LinkLayer, Medium};

/// VirtIO link-layer device.
///
/// Wraps the existing `VirtIONetDevice` and implements `LinkLayer`.
/// The inner device acts as a handle into the global `VIRTIO_NET_DEVICES` registry.
pub struct VirtioLink {
    inner: VirtIONetDevice,
}

impl VirtioLink {
    pub fn new(device_index: usize) -> Self {
        VirtioLink {
            inner: VirtIONetDevice::new(device_index),
        }
    }
}

impl Device for VirtioLink {
    type RxToken<'a> = VirtIONetRxToken where Self: 'a;
    type TxToken<'a> = VirtIONetTxToken where Self: 'a;

    fn receive(&mut self, timestamp: Instant) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        self.inner.receive(timestamp)
    }

    fn transmit(&mut self, timestamp: Instant) -> Option<Self::TxToken<'_>> {
        self.inner.transmit(timestamp)
    }

    fn capabilities(&self) -> DeviceCapabilities {
        self.inner.capabilities()
    }
}

impl LinkLayer for VirtioLink {
    fn name(&self) -> String {
        String::from("eth0")
    }

    fn medium(&self) -> Medium {
        Medium::Ethernet
    }

    fn mtu(&self) -> usize {
        self.capabilities().max_transmission_unit
    }

    fn hw_addr(&self) -> Option<HwAddr> {
        // VirtIONetDevice doesn't expose mac directly, use default
        Some(HwAddr::from_ethernet([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]))
    }

    fn kind(&self) -> LinkKind {
        LinkKind::Virtio
    }

    fn can_send(&self) -> bool {
        // Delegate to the virtio net device static
        crate::devices::net::virtio_net_device::with_net_device(0, |net| net.can_send())
            .unwrap_or(false)
    }

    fn can_recv(&self) -> bool {
        crate::devices::net::virtio_net_device::with_net_device(0, |net| net.can_recv())
            .unwrap_or(false)
    }
}