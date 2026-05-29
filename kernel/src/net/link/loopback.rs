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

//! Loopback link-layer device — smoltcp Device + SmoltcpDevice impl.
//!
//! The `LinkLayer` impl for `LoopbackLink` remains in `net::link::loopback`.

use alloc::{string::String, vec};

use smoltcp::{
    iface::{Interface, SocketSet},
    phy::{Device, DeviceCapabilities, Loopback, Medium as SmoltcpMedium},
    time::Instant,
    wire::{HardwareAddress, IpAddress, IpCidr},
};

use crate::net::{
    link::{HwAddr, LinkKind, LinkLayer, Medium},
    smoltcp::link::SmoltcpDevice,
};

/// Loopback link-layer device.
pub struct LoopbackLink {
    inner: Loopback,
}

impl LoopbackLink {
    pub fn new() -> Self {
        LoopbackLink {
            inner: Loopback::new(SmoltcpMedium::Ip),
        }
    }
}

impl Device for LoopbackLink {
    type RxToken<'a>
        = <Loopback as Device>::RxToken<'a>
    where
        Self: 'a;
    type TxToken<'a>
        = <Loopback as Device>::TxToken<'a>
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

impl LinkLayer for LoopbackLink {
    fn name(&self) -> String {
        String::from("lo")
    }

    fn medium(&self) -> Medium {
        Medium::Ip
    }

    fn mtu(&self) -> usize {
        self.capabilities().max_transmission_unit
    }

    fn hw_addr(&self) -> Option<HwAddr> {
        None
    }

    fn kind(&self) -> LinkKind {
        LinkKind::Loopback
    }

    fn can_send(&self) -> bool {
        true
    }

    fn can_recv(&self) -> bool {
        true
    }
}

impl SmoltcpDevice for LoopbackLink {
    fn create_smoltcp_iface(&mut self) -> (Interface, SocketSet<'static>) {
        use smoltcp::iface::Config;

        let caps = self.capabilities();
        let config = match caps.medium {
            smoltcp::phy::Medium::Ethernet => {
                Config::new(HardwareAddress::Ethernet(smoltcp::wire::EthernetAddress([
                    0x02, 0x00, 0x00, 0x00, 0x00, 0x01,
                ])))
            }
            smoltcp::phy::Medium::Ip => Config::new(HardwareAddress::Ip),
            smoltcp::phy::Medium::Ieee802154 => todo!(),
        };
        let mut iface = Interface::new(
            config,
            &mut self.inner,
            Instant::from_millis(i64::try_from(crate::time::now().as_millis()).unwrap_or(0)),
        );
        if caps.medium == smoltcp::phy::Medium::Ip {
            iface.update_ip_addrs(|addrs| {
                let _ = addrs.push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8));
                let _ = addrs.push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128));
            });
        }
        let sockets = SocketSet::new(vec![]);
        (iface, sockets)
    }

    fn poll_smoltcp(&mut self, timestamp: Instant, iface: &mut Interface, sockets: &mut SocketSet) {
        iface.poll(timestamp, &mut self.inner, sockets);
    }
}
