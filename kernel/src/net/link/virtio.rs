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

//! VirtIO link-layer device — smoltcp Device + SmoltcpDevice impl.
//!
//! The `LinkLayer` impl for `VirtioLink` remains in `net::link::virtio`.

use alloc::{string::String, vec};

use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{Device, DeviceCapabilities, Medium as SmoltcpMedium},
    time::Instant,
    wire::{EthernetAddress, HardwareAddress, IpAddress, IpCidr, Ipv4Address},
};

use crate::{
    devices::net::virtio_net_device::{VirtIONetDevice, VirtIONetRxToken, VirtIONetTxToken},
    net::link::{HwAddr, LinkKind, LinkLayer, Medium},
    net::smoltcp::link::SmoltcpDevice,
};

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
    type RxToken<'a>
        = VirtIONetRxToken
    where
        Self: 'a;
    type TxToken<'a>
        = VirtIONetTxToken
    where
        Self: 'a;

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
        Some(HwAddr::from_ethernet([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]))
    }

    fn kind(&self) -> LinkKind {
        LinkKind::Virtio
    }

    fn can_send(&self) -> bool {
        crate::devices::net::virtio_net_device::with_net_device(0, |net| net.can_send())
            .unwrap_or(false)
    }

    fn can_recv(&self) -> bool {
        crate::devices::net::virtio_net_device::with_net_device(0, |net| net.can_recv())
            .unwrap_or(false)
    }
}

impl SmoltcpDevice for VirtioLink {
    fn create_smoltcp_iface(&mut self) -> (Interface, SocketSet<'static>) {
        let caps = self.capabilities();
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
            &mut self.inner,
            Instant::from_millis(i64::try_from(crate::time::now().as_millis()).unwrap_or(0)),
        );
        match caps.medium {
            smoltcp::phy::Medium::Ethernet => {
                iface.update_ip_addrs(|addrs| {
                    let _ = addrs.push(IpCidr::new(IpAddress::v4(10, 0, 2, 15), 24));
                });
                iface
                    .routes_mut()
                    .add_default_ipv4_route(Ipv4Address::new(10, 0, 2, 2));
            }
            smoltcp::phy::Medium::Ip => {
                iface.update_ip_addrs(|addrs| {
                    let _ = addrs.push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8));
                    let _ = addrs.push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128));
                });
            }
            smoltcp::phy::Medium::Ieee802154 => {}
        }
        let sockets = SocketSet::new(vec![]);
        (iface, sockets)
    }

    fn poll_smoltcp(&mut self, timestamp: Instant, iface: &mut Interface, sockets: &mut SocketSet) {
        iface.poll(timestamp, &mut self.inner, sockets);
    }
}