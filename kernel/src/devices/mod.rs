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

use crate::error::Error;
use alloc::{collections::BTreeMap, string::String, sync::Arc};
use core::{
    fmt::Debug,
    sync::atomic::{AtomicU32, Ordering},
};
use embedded_io::ErrorKind;
use libc::*;
use spin::{Once, RwLock as SpinRwLock};
#[cfg(virtio)]
pub mod block;
pub mod console;
pub(crate) mod dumb;
mod error;
pub(crate) mod net;
mod null;
pub mod tty;
#[cfg(virtio)]
pub mod virtio;
mod zero;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DeviceClass {
    Char,
    Block,
    Misc,
}

/// general device commands
///
/// - 0x01 - 0x1F: general device control commands
/// - 0x20 - 0x3F: udevice control commands
/// - 0x40+: special device control commands
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceRequest {
    Resume = 0x01,       // resume device
    Suspend = 0x02,      // suspend device
    Config = 0x03,       // configure device
    Close = 0x04,        // close device
    NotSupported = 0x00, // not supported
}

impl From<u32> for DeviceRequest {
    fn from(value: u32) -> Self {
        match value {
            0x01 => Self::Resume,
            0x02 => Self::Suspend,
            0x03 => Self::Config,
            0x04 => Self::Close,
            _ => Self::NotSupported,
        }
    }
}

/// Mask for control commands
pub const DEVICE_GENERAL_REQUEST_MASK: u32 = 0x1f;

#[derive(Debug)]
pub struct DeviceBase {
    pub open_count: AtomicU32,
}

impl DeviceBase {
    pub fn new() -> Self {
        Self {
            open_count: AtomicU32::new(0),
        }
    }

    pub fn inc_open_count(&self) -> u32 {
        self.open_count.fetch_add(1, Ordering::Relaxed)
    }

    pub fn dec_open_count(&self) -> u32 {
        self.open_count.fetch_sub(1, Ordering::Relaxed)
    }

    pub fn is_opened(&self) -> bool {
        self.open_count.load(Ordering::Relaxed) > 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeviceId(usize);

impl DeviceId {
    /// Create a new DeviceId from major and minor numbers
    pub fn new(major: usize, minor: usize) -> Self {
        #[cfg(target_pointer_width = "32")]
        {
            // On 32-bit platforms: major in high 12 bits, minor in low 20 bits
            let major_part = major << 20;
            let minor_part = minor & 0xFFFFF; // 20 bits
            Self(major_part | minor_part)
        }

        #[cfg(target_pointer_width = "64")]
        {
            // On 64-bit platforms: major in high 20 bits, minor in low 44 bits
            let major_part = major << 44;
            let minor_part = minor & 0xFFFFFFFFFFF; // 44 bits
            Self(major_part | minor_part)
        }
    }

    /// Get the major device number
    pub fn major(&self) -> usize {
        #[cfg(target_pointer_width = "32")]
        {
            // Extract high 12 bits
            (self.0 >> 20) & 0xFFF
        }

        #[cfg(target_pointer_width = "64")]
        {
            // Extract high 20 bits
            (self.0 >> 44) & 0xFFFFF
        }
    }

    /// Get the minor device number
    pub fn minor(&self) -> usize {
        #[cfg(target_pointer_width = "32")]
        {
            // Extract low 20 bits
            self.0 & 0xFFFFF
        }

        #[cfg(target_pointer_width = "64")]
        {
            // Extract low 44 bits
            self.0 & 0xFFFFFFFFFFF
        }
    }

    /// Get the raw usize value
    pub fn raw(&self) -> usize {
        self.0
    }

    /// Create from raw usize value
    pub fn from_raw(raw: usize) -> Self {
        Self(raw)
    }
}

impl From<usize> for DeviceId {
    fn from(raw: usize) -> Self {
        Self::from_raw(raw)
    }
}

impl From<DeviceId> for usize {
    fn from(device_id: DeviceId) -> Self {
        device_id.raw()
    }
}

pub trait Device: Send + Sync {
    fn name(&self) -> String;
    fn class(&self) -> DeviceClass;
    fn id(&self) -> DeviceId;
    fn open(&self) -> Result<(), ErrorKind> {
        Ok(())
    }
    fn close(&self) -> Result<(), ErrorKind> {
        Ok(())
    }
    fn read(&self, pos: u64, buf: &mut [u8], is_nonblocking: bool) -> Result<usize, ErrorKind>;
    fn write(&self, pos: u64, buf: &[u8], is_nonblocking: bool) -> Result<usize, ErrorKind>;
    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        Err(ErrorKind::Unsupported)
    }
    /// Returns the device capacity.
    /// For block devices, returns the number of sectors
    fn capacity(&self) -> Result<u64, ErrorKind> {
        Err(ErrorKind::Unsupported)
    }
    fn sector_size(&self) -> Result<u16, ErrorKind> {
        Err(ErrorKind::Unsupported)
    }
    fn sync(&self) -> Result<(), ErrorKind> {
        Err(ErrorKind::Unsupported)
    }
}

impl Debug for dyn Device {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("Device")
            .field("name", &self.name())
            .field("class", &self.class())
            .field("id", &self.id())
            .finish()
    }
}

static DEVICE_MANAGER: Once<DeviceManager> = Once::new();

pub struct DeviceManager {
    pub char_devices: SpinRwLock<BTreeMap<String, Arc<dyn Device>>>,
    pub block_devices: SpinRwLock<BTreeMap<String, Arc<dyn Device>>>,
    pub misc_devices: SpinRwLock<BTreeMap<String, Arc<dyn Device>>>,
}

impl DeviceManager {
    pub fn new() -> Self {
        Self {
            char_devices: SpinRwLock::new(BTreeMap::new()),
            block_devices: SpinRwLock::new(BTreeMap::new()),
            misc_devices: SpinRwLock::new(BTreeMap::new()),
        }
    }

    pub fn get() -> &'static DeviceManager {
        DEVICE_MANAGER.call_once(DeviceManager::new)
    }

    pub fn get_device_number(&self) -> usize {
        self.char_devices.read().len()
            + self.block_devices.read().len()
            + self.misc_devices.read().len()
    }

    pub fn register_device(&self, name: String, dev: Arc<dyn Device>) -> Result<(), ErrorKind> {
        match dev.class() {
            DeviceClass::Char => {
                let mut devices = self.char_devices.write();
                devices
                    .try_insert(name, dev)
                    .map_err(|_| ErrorKind::AlreadyExists)?;
            }
            DeviceClass::Block => {
                let mut devices = self.block_devices.write();
                devices
                    .try_insert(name, dev)
                    .map_err(|_| ErrorKind::AlreadyExists)?;
            }
            DeviceClass::Misc => {
                let mut devices = self.misc_devices.write();
                devices
                    .try_insert(name, dev)
                    .map_err(|_| ErrorKind::AlreadyExists)?;
            }
        };
        Ok(())
    }

    pub fn get_block_device(&self, str: &str) -> Option<Arc<dyn Device>> {
        self.block_devices.read().get(str).cloned()
    }

    pub fn get_char_device(&self, str: &str) -> Option<Arc<dyn Device>> {
        self.char_devices.read().get(str).cloned()
    }

    pub fn get_misc_device(&self, str: &str) -> Option<Arc<dyn Device>> {
        self.misc_devices.read().get(str).cloned()
    }

    pub fn foreach<F>(&self, callback: F) -> Result<(), Error>
    where
        F: Fn(&str, Arc<dyn Device>) -> Result<(), Error>,
    {
        {
            let char_devices = self.char_devices.read();
            for (name, device) in char_devices.iter() {
                callback(name, device.clone())?
            }
        }
        {
            let block_devices = self.block_devices.read();
            for (name, device) in block_devices.iter() {
                callback(name, device.clone())?
            }
        }
        {
            let misc_devices = self.misc_devices.read();
            for (name, device) in misc_devices.iter() {
                callback(name, device.clone())?
            }
        }
        Ok(())
    }
}

pub fn init() -> Result<(), Error> {
    null::Null::register().map_err(Error::from)?;
    zero::Zero::register().map_err(Error::from)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_device_id_creation() {
        let device_id = DeviceId::new(123, 456);
        assert_eq!(device_id.major(), 123);
        assert_eq!(device_id.minor(), 456);
    }

    #[test]
    fn test_device_id_from_usize() {
        let device_id = DeviceId::new(123, 456);
        let raw_value = device_id.raw();
        let device_id_from_raw = DeviceId::from_raw(raw_value);
        assert_eq!(device_id.major(), device_id_from_raw.major());
        assert_eq!(device_id.minor(), device_id_from_raw.minor());
    }

    #[test]
    fn test_device_id_conversion() {
        let device_id = DeviceId::new(123, 456);
        let raw_value: usize = device_id.into();
        let device_id_from_raw = DeviceId::from(raw_value);
        assert_eq!(device_id.major(), device_id_from_raw.major());
        assert_eq!(device_id.minor(), device_id_from_raw.minor());
    }

    #[test]
    fn test_device_id_bit_allocation() {
        // Test maximum values for each platform
        #[cfg(target_pointer_width = "32")]
        {
            // On 32-bit: major (12 bits max), minor (20 bits max)
            let device_id = DeviceId::new(0xFFF, 0xFFFFF);
            assert_eq!(device_id.major(), 0xFFF);
            assert_eq!(device_id.minor(), 0xFFFFF);

            // Test overflow handling
            let device_id = DeviceId::new(0x1FFF, 0x1FFFFF); // Values larger than bit fields
            assert_eq!(device_id.major(), 0xFFF); // Should be truncated to 12 bits
            assert_eq!(device_id.minor(), 0xFFFFF); // Should be truncated to 20 bits
        }

        #[cfg(target_pointer_width = "64")]
        {
            // On 64-bit: major (20 bits max), minor (44 bits max)
            let device_id = DeviceId::new(0xFFFFF, 0xFFFFFFFFFFF);
            assert_eq!(device_id.major(), 0xFFFFF);
            assert_eq!(device_id.minor(), 0xFFFFFFFFFFF);

            // Test overflow handling
            let device_id = DeviceId::new(0x1FFFFF, 0x1FFFFFFFFFFF); // Values larger than bit fields
            assert_eq!(device_id.major(), 0xFFFFF); // Should be truncated to 20 bits
            assert_eq!(device_id.minor(), 0xFFFFFFFFFFF); // Should be truncated to 44 bits
        }
    }
}
