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

use bme280::i2c::BME280;
use embedded_hal::delay::DelayNs;

use crate::{
    devices::DeviceData,
    drivers::{Driver, DriverModule},
    scheduler,
};

struct KernelDelay;

impl DelayNs for KernelDelay {
    fn delay_ns(&mut self, ns: u32) {
        let ticks = blueos_kconfig::TICKS_PER_SECOND as u32 * ns / 1_000_000_000;
        if ticks == 0 {
            scheduler::yield_me();
        } else {
            scheduler::suspend_me_for(ticks as _);
        }
    }
}

pub struct Bme280Config {
    pub device_addr: u8,
}

#[derive(Default)]
pub struct Bme280 {
    device_addr: u8,
}

impl Driver for Bme280 {
    fn init(self) -> crate::drivers::Result<Self> {
        match self.device_addr {
            0x76 => {}
            0x77 => {}
            _ => return Err(crate::error::code::EINVAL),
        }

        Ok(self)
    }
}

pub struct Bme280DriverModule {}

impl DriverModule for Bme280DriverModule {
    type Data = Bme280;
    fn probe(dev: &crate::devices::DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if let Some(config) = native_dev.config::<Bme280Config>() {
                    Ok(Bme280 {
                        device_addr: config.device_addr,
                    })
                } else {
                    Err(crate::error::code::ENODEV)
                }
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}
