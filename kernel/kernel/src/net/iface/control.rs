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

use crate::{
    alloc::borrow::ToOwned,
    net::link::{
        link_kind::LinkKind,
        wifi_ops::{WifiScanConfig, WifiScanResult},
    },
};
use alloc::{string::String, vec::Vec};
use core::ptr;
use smoltcp::wire::IpCidr;

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
    /// Scan for WiFi networks with the given configuration.
    WifiScan(WifiScanConfig),
    /// Cache the WiFi passphrase (sent by SIOCSIWENCODE before SIOCSIWESSID).
    WifiPassphrase(String),
    /// Connect to a WiFi network.
    WifiConnect { ifname: [u8; 16], ssid: String },
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
                if arg == 0 {
                    return Err(NetIfaceError::InvalidParam);
                }

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
                if arg == 0 {
                    return Err(NetIfaceError::InvalidParam);
                }

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
                if arg == 0 {
                    return Err(NetIfaceError::InvalidParam);
                }

                let mtu = unsafe { ptr::read_unaligned(arg as *const i32) };
                Ok(NetIfaceControl::SetMtu(mtu as usize))
            }
            // SIOCSIWSCAN (0x8B18) — trigger WiFi scan with optional SSID filter
            0x8B18 => {
                // arg: pointer to struct iwreq
                //   ifrn_name: [i8; 16]  at offset 0
                //   u.essid (iw_point):  at offset 16
                //     pointer: *mut c_void  (4 bytes on riscv32)
                //     length:  u16          (2 bytes)
                //     flags:   u16          (2 bytes)
                let mut ifrn_name = [0u8; 16];
                unsafe {
                    ptr::copy_nonoverlapping(arg as *const u8, ifrn_name.as_mut_ptr(), 16);
                }

                let iwreq_arg = arg + 16;
                let essid_ptr =
                    unsafe { ptr::read_unaligned(iwreq_arg as *const *mut core::ffi::c_void) };
                let essid_len = unsafe {
                    ptr::read_unaligned(
                        (iwreq_arg + core::mem::size_of::<*mut core::ffi::c_void>()) as *const u16,
                    )
                } as usize;

                // When length > IW_ESSID_MAX_SIZE (32), the pointer is to a
                // struct iw_scan_req whose first byte is scan_type. When
                // length <= 32 it's a bare SSID string and we use active (0).
                let scan_type = if essid_len > 32 && !essid_ptr.is_null() {
                    unsafe { ptr::read_unaligned(essid_ptr as *const u8) }
                } else {
                    0
                };

                let mut buf = [0u8; 32];
                if !essid_ptr.is_null() && essid_len > 0 && essid_len <= 32 {
                    unsafe {
                        ptr::copy_nonoverlapping(
                            essid_ptr as *const u8,
                            buf.as_mut_ptr(),
                            essid_len,
                        );
                    }
                }

                Ok(NetIfaceControl::WifiScan(WifiScanConfig {
                    ifname: ifrn_name,
                    ssid: if essid_len > 0 && essid_len <= 32 && !essid_ptr.is_null() {
                        Some(unsafe {
                            core::str::from_utf8_unchecked(&buf[..essid_len]).to_owned()
                        })
                    } else {
                        None
                    },
                    scan_type,
                    channel: 0,
                }))
            }
            // SIOCSIWENCODE (0x8B2A) — set WiFi passphrase
            // The passphrase is cached globally; the actual connect is triggered
            // by the subsequent SIOCSIWESSID ioctl.
            0x8B2A => {
                // arg: pointer to struct iwreq
                //   ifrn_name: [i8; 16]  at offset 0
                //   u.encoding (iw_point):  at offset 16
                //     pointer: *mut c_void  (4 bytes on riscv32)
                //     length:  u16          (2 bytes)
                //     flags:   u16          (2 bytes)
                let iwreq_arg = arg + 16;
                let enc_ptr =
                    unsafe { ptr::read_unaligned(iwreq_arg as *const *mut core::ffi::c_void) };
                let enc_len = unsafe {
                    ptr::read_unaligned(
                        (iwreq_arg + core::mem::size_of::<*mut core::ffi::c_void>()) as *const u16,
                    )
                } as usize;

                let passphrase = if !enc_ptr.is_null() && enc_len > 0 && enc_len <= 64 {
                    let mut buf = [0u8; 64];
                    unsafe {
                        ptr::copy_nonoverlapping(enc_ptr as *const u8, buf.as_mut_ptr(), enc_len);
                    }
                    String::from_utf8_lossy(&buf[..enc_len]).into_owned()
                } else {
                    String::new()
                };

                Ok(NetIfaceControl::WifiPassphrase(passphrase))
            }
            // SIOCSIWESSID (0x8B1A) — trigger WiFi connect
            0x8B1A => {
                // arg: pointer to struct iwreq
                //   ifrn_name: [i8; 16]  at offset 0
                //   u.essid (iw_point):  at offset 16
                //     pointer: *mut c_void  (4 bytes on riscv32)
                //     length:  u16          (2 bytes)
                //     flags:   u16          (2 bytes)
                let mut ifrn_name = [0u8; 16];
                unsafe {
                    ptr::copy_nonoverlapping(arg as *const u8, ifrn_name.as_mut_ptr(), 16);
                }

                let iwreq_arg = arg + 16;
                let essid_ptr =
                    unsafe { ptr::read_unaligned(iwreq_arg as *const *mut core::ffi::c_void) };
                let essid_len = unsafe {
                    ptr::read_unaligned(
                        (iwreq_arg + core::mem::size_of::<*mut core::ffi::c_void>()) as *const u16,
                    )
                } as usize;

                let ssid = if !essid_ptr.is_null() && essid_len > 0 && essid_len <= 32 {
                    let mut buf = [0u8; 32];
                    unsafe {
                        ptr::copy_nonoverlapping(
                            essid_ptr as *const u8,
                            buf.as_mut_ptr(),
                            essid_len,
                        );
                    }
                    String::from_utf8_lossy(&buf[..essid_len]).into_owned()
                } else {
                    String::new()
                };

                Ok(NetIfaceControl::WifiConnect {
                    ifname: ifrn_name,
                    ssid,
                })
            }
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
