// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use core::cell::RefCell;

use crate::{
    net::net_interface::{NetDevice, NetInterface},
    time::TickTime,
};
use alloc::{rc::Rc, vec};
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{Device, Medium},
    time::{Duration, Instant},
    wire::{EthernetAddress, IpAddress, IpCidr},
};

/// Use smoltcp::phy::Loopback as inner net device
/// Add SmoltcpNetInterface wrapper to smoltcp::phy::Loopback device
impl NetInterface<'_> {
    pub fn create_loopback_interface() -> Self {
        let mut inner = smoltcp::phy::Loopback::new(Medium::Ip);

        // Create Device
        let mut socket_set = SocketSet::new(vec![]);

        // Create interface
        let mut config = match inner.capabilities().medium {
            Medium::Ethernet => {
                Config::new(EthernetAddress([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]).into())
            }
            Medium::Ip => Config::new(smoltcp::wire::HardwareAddress::Ip),
            Medium::Ieee802154 => todo!(),
        };

        let mut interface = Interface::new(
            config,
            &mut inner,
            Instant::from_millis(i64::try_from(TickTime::now().as_millis()).unwrap_or(0)),
        );

        interface.update_ip_addrs(|ip_addrs| {
            if ip_addrs
                .push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8)) // local ip
                .is_err()
            {
                log::error!("Add ip v4 addrs to loopback device fail");
            };

            if ip_addrs
                .push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128))
                .is_err()
            {
                log::error!("Add ip v6 addrs to loopback device fail");
            };
        });

        let device = Rc::new(RefCell::new(NetDevice::Loopback(inner)));

        let interface = Rc::new(RefCell::new(interface));
        let socket_set = Rc::new(RefCell::new(socket_set));

        NetInterface::new("Loopback".into(), device, interface, socket_set)
    }
}
