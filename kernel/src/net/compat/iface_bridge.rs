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

//! Smoltcp `Interface` creation helpers.
//!
//! Provides functions to create a smoltcp `Interface` from a concrete
//! link-layer device that implements both `Device` and `LinkLayer`.
//!
//! NOTE: The `smoltcp::phy::Device` trait uses GATs and is NOT
//! dyn-compatible. This module works with concrete types only.
//! It will be removed in Phase 2 when smoltcp is phased out.

use smoltcp::iface::{Config, Interface};
use smoltcp::phy::Device;
use smoltcp::time::Instant;
use smoltcp::wire::{EthernetAddress, HardwareAddress, IpAddress, IpCidr};

use crate::time;

use crate::net::link::Medium;

/// Create a smoltcp `Interface` from a concrete link-layer device.
///
/// `D` must implement both `smoltcp::phy::Device` and the traits needed
/// for interface configuration (medium detection, hardware address).
/// During Phase 0, callers pass concrete types like `LoopbackLink` or
/// `VirtioLink`.
pub fn create_smoltcp_iface(link: &mut (impl Device + ?Sized)) -> Interface {
    let caps = link.capabilities();
    let config = match caps.medium {
        smoltcp::phy::Medium::Ethernet => {
            // Hardware address is obtained at NetIface construction time
            let mac = [0x02, 0x00, 0x00, 0x00, 0x00, 0x01];
            Config::new(HardwareAddress::Ethernet(EthernetAddress(mac)))
        }
        smoltcp::phy::Medium::Ip => Config::new(HardwareAddress::Ip),
        smoltcp::phy::Medium::Ieee802154 => todo!(),
    };

    // TODO(step-8): use hw_addr from the concrete device
    let mut iface = Interface::new(
        config,
        link,
        Instant::from_millis(i64::try_from(time::now().as_millis()).unwrap_or(0)),
    );

    // Assign loopback address for Ip medium
    if caps.medium == smoltcp::phy::Medium::Ip {
        iface.update_ip_addrs(|addrs| {
            let _ = addrs.push(IpCidr::new(IpAddress::v4(127, 0, 0, 1), 8));
            let _ = addrs.push(IpCidr::new(IpAddress::v6(0, 0, 0, 0, 0, 0, 0, 1), 128));
        });
    }

    iface
}