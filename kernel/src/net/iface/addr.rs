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

//! IP address and route configuration types for `NetIface`.

use alloc::vec::Vec;
use smoltcp::wire::IpCidr;

/// IP address configuration for a network interface.
#[derive(Debug, Clone)]
pub struct IpAddrConfig {
    pub addresses: Vec<IpCidr>,
}

impl IpAddrConfig {
    pub const fn new() -> Self {
        IpAddrConfig {
            addresses: Vec::new(),
        }
    }
}

/// A route configuration entry.
#[derive(Debug, Clone)]
pub struct RouteConfig {
    pub destination: IpCidr,
    pub gateway: Option<smoltcp::wire::IpAddress>,
}
