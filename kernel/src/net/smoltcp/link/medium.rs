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

//! Medium conversions between `net::link::Medium` and `smoltcp::phy::Medium`.

use crate::net::link::Medium;

impl From<Medium> for smoltcp::phy::Medium {
    fn from(m: Medium) -> Self {
        match m {
            Medium::Ethernet => smoltcp::phy::Medium::Ethernet,
            Medium::Ip => smoltcp::phy::Medium::Ip,
            Medium::Ieee802154 => smoltcp::phy::Medium::Ieee802154,
        }
    }
}

impl From<smoltcp::phy::Medium> for Medium {
    fn from(m: smoltcp::phy::Medium) -> Self {
        match m {
            smoltcp::phy::Medium::Ethernet => Medium::Ethernet,
            smoltcp::phy::Medium::Ip => Medium::Ip,
            smoltcp::phy::Medium::Ieee802154 => Medium::Ieee802154,
        }
    }
}