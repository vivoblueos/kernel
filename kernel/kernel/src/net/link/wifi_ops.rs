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

use crate::net::error::NetError;
use alloc::{string::String, vec::Vec};
use core::{
    any::Any,
    fmt::{Debug, Write},
    sync::atomic::{AtomicUsize, Ordering},
};

/// Result of a WiFi network scan.
#[derive(Debug, Clone)]
pub struct WifiScanResult {
    pub ssid: String,
    pub bssid: [u8; 6],
    pub signal_dbm: i8,
    pub channel: u16,
    pub security: WifiSecurity,
}

#[derive(Debug, Clone)]
pub struct WifiScanConfig {
    /// Interface name (e.g. "wlan0"). Matches `iwreq.ifr_ifrn.ifrn_name`.
    pub ifname: [u8; 16],
    /// Optional SSID filter. If set, only scan for this specific SSID.
    pub ssid: Option<String>,
    /// Scan type: 0 = active (send probe requests), 1 = passive (listen only).
    pub scan_type: u8,
    /// Optional specific channel to scan (0 = scan all channels).
    pub channel: u16,
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
    fn scan(&mut self, config: &WifiScanConfig) -> Result<Vec<WifiScanResult>, NetError>;
    /// Connect to a WiFi network.
    fn connect(&mut self, ssid: &str, passphrase: &str) -> Result<(), NetError>;
    /// Disconnect from the current WiFi network.
    fn disconnect(&mut self) -> Result<(), NetError>;
    /// Get the current signal strength in dBm.
    fn signal_strength(&self) -> Result<i8, NetError>;
}

/// Information about a connected station.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Ssid {
    ssid: [u8; 32],
    len: u8,
}

impl Ssid {
    pub(crate) fn new(ssid: &str) -> Self {
        let mut ssid_bytes = [0u8; 32];
        let bytes = ssid.as_bytes();
        let len = usize::min(32, bytes.len());
        ssid_bytes[..len].copy_from_slice(bytes);

        Self::from_raw(&ssid_bytes, len as u8)
    }

    pub(crate) fn from_raw(ssid: &[u8], len: u8) -> Self {
        let mut ssid_bytes = [0u8; 32];
        let len = usize::min(32, len as usize);
        ssid_bytes[..len].copy_from_slice(&ssid[..len]);

        Self {
            ssid: ssid_bytes,
            len: len as u8,
        }
    }

    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.ssid[..self.len as usize]
    }

    /// The length (in bytes) of the SSID.
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns true if the SSID is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The SSID as a string slice.
    pub fn as_str(&self) -> &str {
        let part = &self.ssid[..self.len as usize];
        match core::str::from_utf8(part) {
            Ok(s) => s,
            Err(e) => {
                let (valid, _) = part.split_at(e.valid_up_to());
                unsafe { core::str::from_utf8_unchecked(valid) }
            }
        }
    }
}

impl Debug for Ssid {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('"')?;
        f.write_str(self.as_str())?;
        f.write_char('"')
    }
}

impl From<alloc::string::String> for Ssid {
    fn from(ssid: alloc::string::String) -> Self {
        Self::new(&ssid)
    }
}

impl From<&str> for Ssid {
    fn from(ssid: &str) -> Self {
        Self::new(ssid)
    }
}

impl From<&[u8]> for Ssid {
    fn from(ssid: &[u8]) -> Self {
        Self::from_raw(ssid, ssid.len() as u8)
    }
}

const WIFI_SCAN_CACHE_IDLE: usize = 0;
const WIFI_SCAN_CACHE_SCANNING: usize = 1;
const WIFI_SCAN_CACHE_READY: usize = 2;

/// Global cache for WiFi scan results. The payload is populated by the WiFi
/// driver's async ScanDone handler and read by `SIOCGIWSCAN` (from `sockfs`).
static WIFI_SCAN_CACHE: spin::Mutex<Option<Vec<WifiScanResult>>> = spin::Mutex::new(None);
static WIFI_SCAN_CACHE_STATE: AtomicUsize = AtomicUsize::new(WIFI_SCAN_CACHE_IDLE);

/// Global cache for the WiFi passphrase, set by SIOCSIWENCODE and consumed by
/// the subsequent SIOCSIWESSID (WifiConnect) ioctl.
static WIFI_PASSPHRASE_CACHE: spin::Mutex<Option<String>> = spin::Mutex::new(None);

/// Mark scan results as pending before starting a new async scan.
pub(crate) fn try_mark_scan_results_pending() -> bool {
    WIFI_SCAN_CACHE_STATE
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |state| {
            if state == WIFI_SCAN_CACHE_SCANNING {
                None
            } else {
                Some(WIFI_SCAN_CACHE_SCANNING)
            }
        })
        .is_ok()
}

/// Mark scan results as unavailable when starting the scan task fails.
pub(crate) fn mark_scan_results_unavailable() {
    WIFI_SCAN_CACHE_STATE.store(WIFI_SCAN_CACHE_IDLE, Ordering::Release);
}

/// Check whether the global WiFi scan cache already has ready results.
pub(crate) fn scan_results_ready() -> bool {
    WIFI_SCAN_CACHE_STATE.load(Ordering::Acquire) == WIFI_SCAN_CACHE_READY
}

/// Replace the global WiFi scan cache with the latest results.
pub(crate) fn update_scan_results_cache(results: Vec<WifiScanResult>) {
    *WIFI_SCAN_CACHE.lock() = Some(results);
    WIFI_SCAN_CACHE_STATE.store(WIFI_SCAN_CACHE_READY, Ordering::Release);
}

/// Copy cached WiFi scan results into a user-space buffer.
///
/// `buf` is a raw pointer to the user-space destination, `buf_len` is its
/// capacity. Returns the number of bytes written on success, or `EINVAL` /
/// `EAGAIN` / `ENOSPC` on error.
pub(crate) fn copy_scan_results_to_user(
    buf: *mut u8,
    buf_len: usize,
) -> Result<usize, crate::error::Error> {
    match WIFI_SCAN_CACHE_STATE.load(Ordering::Acquire) {
        WIFI_SCAN_CACHE_READY => {}
        WIFI_SCAN_CACHE_SCANNING => return Err(crate::error::code::EAGAIN),
        _ => return Err(crate::error::code::EINVAL),
    }

    let cache = WIFI_SCAN_CACHE.lock();
    let results = cache.as_ref().ok_or(crate::error::code::EINVAL)?;

    // Wire format: little-endian u32 count followed by N serialized entries.
    // Each entry: [u32 ssid_len][ssid bytes][u8[6] bssid][i8 signal][u16 channel][u8 security].
    let mut needed = core::mem::size_of::<u32>();
    for ap in results.iter() {
        needed += core::mem::size_of::<u32>()      // ssid_len
            + ap.ssid.len()                         // ssid bytes
            + 6usize                                 // bssid
            + 1usize                                 // signal_dbm
            + 2usize                                 // channel
            + 1usize; // security
    }

    if buf.is_null() {
        return Ok(needed); // query-size-only call
    }
    if buf_len < needed {
        return Err(crate::error::code::ENOSPC);
    }

    let mut offset = 0usize;

    // Write count
    let count = results.len() as u32;
    unsafe {
        core::ptr::write_unaligned(buf.add(offset) as *mut u32, count);
    }
    offset += core::mem::size_of::<u32>();

    for ap in results.iter() {
        // ssid_len
        let ssid_len = ap.ssid.len() as u32;
        unsafe {
            core::ptr::write_unaligned(buf.add(offset) as *mut u32, ssid_len);
        }
        offset += core::mem::size_of::<u32>();

        // ssid bytes
        if !ap.ssid.is_empty() {
            unsafe {
                core::ptr::copy_nonoverlapping(ap.ssid.as_ptr(), buf.add(offset), ap.ssid.len());
            }
            offset += ap.ssid.len();
        }

        // bssid
        unsafe {
            core::ptr::copy_nonoverlapping(ap.bssid.as_ptr(), buf.add(offset), 6);
        }
        offset += 6;

        // signal_dbm
        unsafe {
            core::ptr::write_unaligned(buf.add(offset) as *mut i8, ap.signal_dbm);
        }
        offset += 1;

        // channel
        unsafe {
            core::ptr::write_unaligned(buf.add(offset) as *mut u16, ap.channel);
        }
        offset += 2;

        // security
        let sec = ap.security as u8;
        unsafe {
            core::ptr::write_unaligned(buf.add(offset) as *mut u8, sec);
        }
        offset += 1;
    }

    Ok(needed)
}
