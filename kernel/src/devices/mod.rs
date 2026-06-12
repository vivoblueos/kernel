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

// Re-export core device types from the standalone blueos_devices crate.
pub use blueos_devices::{
    Device, DeviceBase, DeviceClass, DeviceId, DeviceManager, DeviceRequest,
    DEVICE_GENERAL_REQUEST_MASK,
};

use crate::{devices::bus::BusInterface, error::Error};
use alloc::{boxed::Box, sync::Arc, string::String};
use blueos_infra::{
    impl_simple_intrusive_adapter,
    list::typed_atomic_ilist::{AtomicListHead, AtomicListIterator},
};
use core::sync::atomic::AtomicBool;
use embedded_io::ErrorKind;

#[cfg(virtio)]
pub mod block;
pub mod bus;
pub mod clock;
pub mod console;
pub mod dumb;
mod error_conv;
#[cfg(target_arch = "aarch64")]
pub mod fdt;
pub mod i2c_core;
#[cfg(enable_net)]
pub(crate) mod net;
pub mod null;
pub mod tty;
#[cfg(virtio)]
pub mod virtio;
pub mod zero;

#[non_exhaustive]
pub enum DeviceData {
    Native(NativeDevice),
    Zephyr,
}

pub const fn new_native_device_data(config: &'static dyn core::any::Any) -> DeviceData {
    DeviceData::Native(NativeDevice::new(config))
}

type DeviceList = AtomicListHead<DeviceDataNode, Node>;
type DeviceListIterator = AtomicListIterator<DeviceDataNode, Node>;

impl_simple_intrusive_adapter!(Node, DeviceDataNode, node);

#[repr(C)]
pub struct DeviceDataNode {
    pub node: DeviceList,
    pub data: &'static DeviceData,
}

impl DeviceDataNode {
    pub const fn new(data: &'static DeviceData) -> Self {
        Self {
            node: DeviceList::new(),
            data,
        }
    }
}

pub struct NativeDevice {
    config: &'static dyn core::any::Any,
    is_attached: AtomicBool,
}

unsafe impl Send for NativeDevice {}
unsafe impl Sync for NativeDevice {}

impl NativeDevice {
    pub const fn new(config: &'static dyn core::any::Any) -> Self {
        Self {
            config,
            is_attached: AtomicBool::new(false),
        }
    }

    pub fn config<T: 'static>(&self) -> Option<&'static T> {
        self.config.downcast_ref::<T>()
    }

    pub fn is_attached(&self) -> bool {
        self.is_attached.load(core::sync::atomic::Ordering::Relaxed)
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
    use crate::{
        devices::bus::{Bus, BusInterface},
        drivers::*,
    };
    use blueos_test_macro::test;

    #[derive(Debug, Default)]
    struct DummyConfig {
        pub base_addr: usize,
    }

    static DUMMY_CONFIG: DummyConfig = DummyConfig { base_addr: 0x1000 };
    static DUMMY_DEVICE_DATA: DeviceData = DeviceData::Native(NativeDevice::new(&DUMMY_CONFIG));

    #[derive(Default)]
    struct DummyDriver {
        base_addr: usize,
    }

    impl InitDriver<DummyBus> for DummyConfig {
        type Data = DummyDriver;
        fn init(self, bus: &Bus<DummyBus>) -> Result<Self::Data> {
            let ret = DummyDriver {
                base_addr: self.base_addr,
            };
            Ok(ret)
        }
    }

    struct DummyDriverModule;
    impl DriverModule<DummyBus> for DummyDriverModule {
        type Data = DummyConfig;
        fn probe(dev: &DeviceData) -> Result<Self::Data> {
            match dev {
                DeviceData::Native(native_dev) => {
                    if let Some(config) = native_dev.config::<DummyConfig>() {
                        Ok(DummyConfig {
                            base_addr: config.base_addr,
                        })
                    } else {
                        Err(crate::error::code::ENODEV)
                    }
                }
                _ => Err(crate::error::code::ENODEV),
            }
        }
    }

    struct DummyBus;
    impl BusInterface for DummyBus {
        type Region = u8;
        fn read_region(
            &self,
            region: Self::Region,
            buffer: &mut [u8],
        ) -> crate::drivers::Result<()> {
            Ok(())
        }

        fn write_region(&self, region: Self::Region, data: &[u8]) -> crate::drivers::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn test_device_match() {
        let mut dummy_bus = super::bus::Bus::new(DummyBus);
        dummy_bus
            .register_device(&DUMMY_DEVICE_DATA)
            .expect("Failed to register device");
        let driver = dummy_bus.probe_driver(&DummyDriverModule);
        assert!(driver.is_ok());
        let driver = driver.unwrap().init(&dummy_bus);
        assert!(driver.is_ok());
        assert_eq!(driver.unwrap().base_addr, 0x1000);
    }

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
            let device_id = DeviceId::new(0xFFF, 0xFFFFF);
            assert_eq!(device_id.major(), 0xFFF);
            assert_eq!(device_id.minor(), 0xFFFFF);

            let device_id = DeviceId::new(0x1FFF, 0x1FFFFF);
            assert_eq!(device_id.major(), 0xFFF);
            assert_eq!(device_id.minor(), 0xFFFFF);
        }

        #[cfg(target_pointer_width = "64")]
        {
            let device_id = DeviceId::new(0xFFFFF, 0xFFFFFFFFFFF);
            assert_eq!(device_id.major(), 0xFFFFF);
            assert_eq!(device_id.minor(), 0xFFFFFFFFFFF);

            let device_id = DeviceId::new(0x1FFFFF, 0x1FFFFFFFFFFF);
            assert_eq!(device_id.major(), 0xFFFFF);
            assert_eq!(device_id.minor(), 0xFFFFFFFFFFF);
        }
    }
}