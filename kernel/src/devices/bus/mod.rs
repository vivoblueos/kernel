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

use alloc::boxed::Box;
use blueos_infra::tinyarc::TinyArc;


pub struct BusWrapper<B: BusInterface>(pub(crate) TinyArc<SpinLock<B>>);

impl<B: BusInterface> Clone for BusWrapper<B> {
    fn clone(&self) -> Self {
        BusWrapper(self.0.clone())
    }
}

pub struct Bus<B: BusInterface> {
    devices: super::SpinRwLock<super::DeviceList>,
    // FIXME: SpinLock is not a efficient way to protect bus interface
    pub intf: BusWrapper<B>,
}

unsafe impl<B: BusInterface> Send for Bus<B> {}
unsafe impl<B: BusInterface> Sync for Bus<B> {}

pub trait BusInterface: Sync + Send + Sized {
    type Region;
    fn read_region(&self, region: Self::Region, buffer: &mut [u8]) -> crate::drivers::Result<()>;

    fn write_region(&self, region: Self::Region, data: &[u8]) -> crate::drivers::Result<()>;
}

impl<B: BusInterface> Bus<B> {
    pub fn new(intf: B) -> Self {
        Self {
            devices: super::SpinRwLock::new(super::DeviceList::new()),
            intf: BusWrapper(TinyArc::new(SpinLock::new(intf))),
        }
    }

    /// # Safety
    ///
    /// The caller must ensure limited number of devices are registered to the bus,
    /// and the devices won't be unregistered.
    pub fn register_device(&self, dev: &'static super::DeviceData) -> crate::drivers::Result<()> {
        let mut devices = self.devices.write();

        let device_node = Box::leak(Box::new(super::DeviceDataNode::new(dev)));
        super::DeviceList::insert_after(&mut devices, &mut device_node.node);
        Ok(())
    }

    pub fn probe_driver<
        T: crate::drivers::InitDriver<B>,
        M: crate::drivers::DriverModule<B, Data = T>,
    >(
        &self,
        dev: &M,
    ) -> crate::drivers::Result<T> {
        let mut driver = Default::default();
        let devices = self.devices.read();
        let it = super::DeviceListIterator::new(&devices, None);
        let mut matched = false;
        for node in it {
            if let Ok(driv) = M::probe(unsafe { node.as_ref() }.owner().data) {
                driver = driv;
                matched = true;
                break;
            }
        }

        if !matched {
            return Err(crate::error::code::ENODEV);
        }
        Ok(driver)
    }
}
