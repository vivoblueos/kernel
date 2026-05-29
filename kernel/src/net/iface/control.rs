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

//! Type-safe network interface control commands.
//!
//! `NetIfaceControl` is a typed enum that replaces the raw C-style
//! `ioctl(cmd: u32, arg: usize)` pattern. The POSIX ioctl boundary
//! (`SocketFile::ioctl`) is the only place where raw `(cmd, arg)` is
//! converted to/from these typed values.

use alloc::{string::String, vec::Vec};
use core::ptr;

use smoltcp::wire::IpCidr;

use crate::net::link::{link_kind::LinkKind, wifi_ops::WifiScanResult};

/// Type-safe control commands for network interfaces.
///
/// Each variant carries typed parameters. No raw `(u32, usize)` pairs
/// leak past the POSIX ioctl conversion boundary.
pub enum NetIfaceControl {
    // ── Interface state ──
    /// Get interface flags (up, running, etc.).
    GetFlags,
    /// Set interface flags.
    SetFlags(InterfaceFlags),
    /// Get MAC address.
    GetMacAddress,
    /// Set MAC address.
    SetMacAddress([u8; 6]),
    /// Get MTU.
    GetMtu,
    /// Set MTU.
    SetMtu(usize),
    /// Bring the interface up.
    Up,
    /// Bring the interface down.
    Down,
    /// Get link kind (Loopback, Virtio, Wifi, etc.).
    GetLinkKind,

    // ── WiFi operations ──
    /// Scan for WiFi networks.
    WifiScan,
    /// Connect to a WiFi network.
    WifiConnect { ssid: String, passphrase: String },
    /// Disconnect from WiFi.
    WifiDisconnect,
    /// Get WiFi signal strength.
    WifiSignalStrength,

    // ── Ethernet operations ──
    /// Set promiscuous mode.
    EthernetSetPromiscuous(bool),

    // ── IP configuration ──
    /// Add an IP address to the interface.
    AddAddress(IpCidr),
    /// Remove an IP address from the interface.
    RemoveAddress(IpCidr),
    /// Set the default gateway.
    SetGateway(IpCidr),
}

impl NetIfaceControl {
    /// Convert from a raw POSIX ioctl `(cmd, arg)` pair.
    ///
    /// This is the **only** place where raw `(u32, usize)` pairs are
    /// converted into type-safe control commands. Returns
    /// `Err(NetIfaceError::NotSupported)` for unknown commands.
    ///
    /// # Safety
    ///
    /// `arg` is interpreted according to `cmd`. Callers must ensure
    /// that `arg` is a valid pointer (when the command expects one)
    /// and that the pointed-to memory is appropriately sized.
    pub unsafe fn from_raw_ioctl(cmd: u32, arg: usize) -> Result<Self, NetIfaceError> {
        // SIOCGIFNAME, SIOCGIFINDEX, etc. are not yet dispatched
        // here — they are handled before socket ioctl dispatch in
        // the VFS layer.  This covers the subset of commands that
        // reach SocketFile::ioctl.
        match cmd {
            // SIOCGIFFLAGS (0x8913) — get interface flags
            0x8913 => Ok(NetIfaceControl::GetFlags),
            // SIOCSIFFLAGS (0x8914) — set interface flags
            0x8914 => {
                // arg: pointer to struct ifreq, flags at offset 4
                let flags = unsafe { ptr::read_unaligned(arg as *const u16) };
                Ok(NetIfaceControl::SetFlags(InterfaceFlags {
                    up: flags & 1 != 0,
                    running: flags & (1 << 6) != 0,
                    promiscuous: flags & (1 << 3) != 0,
                }))
            }
            // SIOCGIFHWADDR (0x8927) — get hardware address
            0x8927 => Ok(NetIfaceControl::GetMacAddress),
            // SIOCSIFHWADDR (0x8924) — set hardware address
            0x8924 => {
                // arg: pointer to struct ifreq with sa_family + sa_data(14)
                let mut mac = [0u8; 6];
                unsafe {
                    // sa_data starts at offset 2 in struct sockaddr
                    ptr::copy_nonoverlapping((arg + 2) as *const u8, mac.as_mut_ptr(), 6);
                }
                Ok(NetIfaceControl::SetMacAddress(mac))
            }
            // SIOCGIFMTU (0x8921) — get MTU
            0x8921 => Ok(NetIfaceControl::GetMtu),
            // SIOCSIFMTU (0x8922) — set MTU
            0x8922 => {
                let mtu = unsafe { ptr::read_unaligned(arg as *const i32) };
                Ok(NetIfaceControl::SetMtu(mtu as usize))
            }
            // SIOCADDRT / SIOCDELRT — routing (not yet implemented)
            // SIOCSIFFLAGS-like WiFi extension commands
            _ => Err(NetIfaceError::NotSupported),
        }
    }
}

/// Interface flags bitmask.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InterfaceFlags {
    pub up: bool,
    pub running: bool,
    pub promiscuous: bool,
}

impl InterfaceFlags {
    pub const fn default() -> Self {
        InterfaceFlags {
            up: false,
            running: false,
            promiscuous: false,
        }
    }
}

/// Result values returned by `NetIface::control()`.
pub enum NetIfaceResult {
    Flags(InterfaceFlags),
    MacAddress([u8; 6]),
    Mtu(usize),
    LinkKind(LinkKind),
    WifiScanResult(Vec<WifiScanResult>),
    WifiSignalStrength(i8),
    Void,
}

/// Errors that can occur during `NetIface::control()`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NetIfaceError {
    DeviceNotFound,
    DeviceTraitNotAvailable,
    InterfaceNotInitialized,
    NotSupported,
    InvalidParam,
    LockFail,
}

impl core::fmt::Display for NetIfaceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NetIfaceError::DeviceNotFound => write!(f, "Device not found"),
            NetIfaceError::DeviceTraitNotAvailable => write!(f, "Device trait not available"),
            NetIfaceError::InterfaceNotInitialized => write!(f, "Interface not initialized"),
            NetIfaceError::NotSupported => write!(f, "Not supported"),
            NetIfaceError::InvalidParam => write!(f, "Invalid parameter"),
            NetIfaceError::LockFail => write!(f, "Lock failed"),
        }
    }
}
