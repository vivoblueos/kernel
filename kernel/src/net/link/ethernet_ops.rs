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

//! Device-specific Ethernet operations trait.
//!
//! This trait is NOT part of `LinkLayer`. It is accessed by downcasting
//! from `dyn LinkLayer` to `dyn EthernetOps` (via `Any`). This keeps
//! `LinkLayer` free of ioctl-like type-unsafe methods.

use core::any::Any;

use crate::net::error::NetError;

/// Device-specific Ethernet operations.
///
/// Accessed via `(link as &dyn Any).downcast_ref::<dyn EthernetOps>()`.
pub trait EthernetOps: Send + Sync + Any + 'static {
    /// Enable or disable promiscuous mode.
    fn set_promiscuous(&mut self, enabled: bool) -> Result<(), NetError>;
    /// Check if promiscuous mode is enabled.
    fn promiscuous(&self) -> bool;
}
