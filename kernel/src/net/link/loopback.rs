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

//! Loopback link-layer device.
//!
//! Wraps `smoltcp::phy::Loopback` and implements `LinkLayer`.

use alloc::string::String;

use smoltcp::phy::{Device, DeviceCapabilities, Loopback, Medium as SmoltcpMedium};
use smoltcp::time::Instant;

use crate::net::link::{HwAddr, LinkKind, LinkLayer, Medium};

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
    type RxToken<'a> = <Loopback as Device>::RxToken<'a> where Self: 'a;
    type TxToken<'a> = <Loopback as Device>::TxToken<'a> where Self: 'a;

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