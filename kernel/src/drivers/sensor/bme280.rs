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

use blueos_driver::i2c::I2cConfig;
use blueos_hal::PlatPeri;
use blueos_infra::tinyarc::TinyArc;
use bme280::i2c::BME280;
use embedded_hal::delay::DelayNs;

use crate::{
    devices::{bus::Bus, i2c_core::block_i2c::BlockI2c, DeviceData},
    drivers::{DriverModule, InitDriver},
    scheduler,
    sync::SpinLock,
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

#[derive(Default)]
pub struct Bme280Config {
    pub device_addr: u8,
}

#[derive(Default)]
pub struct Bme280Driver {
    device_addr: u8,
}

impl Bme280Config {
    pub const fn new(device_addr: u8) -> Self {
        Bme280Config { device_addr }
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> InitDriver<BlockI2c<T>> for Bme280Config {
    type Driver = Bme280Driver;
    fn init(self, bus: &Bus<BlockI2c<T>>) -> crate::drivers::Result<Self::Driver> {
        let mut delay = KernelDelay;

        let mut bme280 = match self.device_addr {
            0x76 => BME280::new_primary(bus.intf.clone()),
            0x77 => BME280::new_secondary(bus.intf.clone()),
            _ => return Err(crate::error::code::EINVAL),
        };

        if let Err(e) = bme280.init(&mut delay) {
            crate::kprintln!("BME280 init failed: {:?}", e);
        } else {
            crate::kprintln!(
                "BME280 initialized successfully at address 0x{:X}",
                self.device_addr
            );
        }

        Ok(Bme280Driver {
            device_addr: self.device_addr,
        })
    }
}

pub struct Bme280DriverModule;

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> DriverModule<BlockI2c<T>> for Bme280DriverModule {
    type Data = Bme280Config;
    fn probe(dev: &crate::devices::DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if let Some(config) = native_dev.config::<Bme280Config>() {
                    Ok(Bme280Config {
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
