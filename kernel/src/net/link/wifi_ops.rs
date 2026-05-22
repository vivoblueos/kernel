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

//! Device-specific WiFi operations trait.
//!
//! This trait is NOT part of `LinkLayer`. It is accessed by downcasting
//! from `dyn LinkLayer` to `dyn WifiOps` (via `Any`). This keeps
//! `LinkLayer` free of ioctl-like type-unsafe methods.

use alloc::{string::String, vec::Vec};
use core::any::Any;

use crate::net::error::NetError;

/// Result of a WiFi network scan.
#[derive(Debug, Clone)]
pub struct WifiScanResult {
    pub ssid: String,
    pub bssid: [u8; 6],
    pub signal_dbm: i8,
    pub channel: u16,
    pub security: WifiSecurity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WifiSecurity {
    Open,
    Wep,
    Wpa,
    Wpa2,
    Wpa3,
    Unknown,
}

/// Device-specific WiFi operations.
///
/// Accessed via `(link as &dyn Any).downcast_ref::<dyn WifiOps>()`.
pub trait WifiOps: Send + Sync + Any + 'static {
    /// Scan for available WiFi networks.
    fn scan(&mut self) -> Result<Vec<WifiScanResult>, NetError>;
    /// Connect to a WiFi network.
    fn connect(&mut self, ssid: &str, passphrase: &str) -> Result<(), NetError>;
    /// Disconnect from the current WiFi network.
    fn disconnect(&mut self) -> Result<(), NetError>;
    /// Get the current signal strength in dBm.
    fn signal_strength(&self) -> Result<i8, NetError>;
}