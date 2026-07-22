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
use bme280::i2c::BME280;
use embedded_hal::delay::DelayNs;
use embedded_io::ErrorKind;

use crate::{
    devices::{
        bus::{Bus, BusWrapper},
        i2c_core::block_i2c::BlockI2c,
        Device, DeviceClass, DeviceData, DeviceId, DeviceManager,
    },
    drivers::{DriverModule, InitDriver},
    sync::{KernelDelay, SpinLock},
};
use alloc::{string::String, sync::Arc};

const BME280_RESET_DELAY_MS: u32 = 2;
const BME280_SAFE_RESET_DELAY_MS: u32 = 10;
const BME280_DEVICE_NAME: &str = "bme2800";
const BME280_DEVICE_MAJOR: usize = 241;
const BME280_DEVICE_MINOR: usize = 0;

/// Binary measurement report returned by `/dev/bme2800`.
///
/// Layout (all multi-byte fields are little-endian):
/// - byte 0: format version (`1`)
/// - bytes 1..=4: temperature in milli-degrees Celsius (`i32`)
/// - bytes 5..=8: pressure in pascals (`u32`)
/// - bytes 9..=12: relative humidity in thousandths of a percent (`u32`)
pub const BME280_REPORT_SIZE: usize = 13;
const BME280_REPORT_VERSION: u8 = 1;

/// Extends the BME280 crate's nominal post-reset delay so the sensor has
/// enough time to copy its NVM calibration data before initialization reads it.
struct Bme280Delay(KernelDelay);

impl DelayNs for Bme280Delay {
    fn delay_ns(&mut self, ns: u32) {
        self.0.delay_ns(ns);
    }

    fn delay_ms(&mut self, ms: u32) {
        let ms = if ms == BME280_RESET_DELAY_MS {
            BME280_SAFE_RESET_DELAY_MS
        } else {
            ms
        };
        self.0.delay_ms(ms);
    }
}

#[derive(Default)]
pub struct Bme280Config {
    pub device_addr: u8,
}

pub struct Bme280Device<T: blueos_hal::i2c::I2c<I2cConfig, ()>> {
    sensor: SpinLock<BME280<BusWrapper<BlockI2c<T>>>>,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> Bme280Device<T> {
    fn new(sensor: BME280<BusWrapper<BlockI2c<T>>>) -> Self {
        Self {
            sensor: SpinLock::new(sensor),
        }
    }

    fn encode_report(
        temperature: f32,
        pressure: f32,
        humidity: f32,
        report: &mut [u8; BME280_REPORT_SIZE],
    ) {
        let temperature_milli_celsius = (temperature * 1_000.0) as i32;
        let pressure_pascals = pressure as u32;
        let humidity_milli_percent = (humidity * 1_000.0) as u32;

        report[0] = BME280_REPORT_VERSION;
        report[1..5].copy_from_slice(&temperature_milli_celsius.to_le_bytes());
        report[5..9].copy_from_slice(&pressure_pascals.to_le_bytes());
        report[9..13].copy_from_slice(&humidity_milli_percent.to_le_bytes());
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> Device for Bme280Device<T> {
    fn name(&self) -> String {
        String::from(BME280_DEVICE_NAME)
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(BME280_DEVICE_MAJOR, BME280_DEVICE_MINOR)
    }

    fn read(
        &self,
        _pos: u64,
        buf: &mut [u8],
        _is_nonblocking: bool,
    ) -> core::result::Result<usize, ErrorKind> {
        if buf.len() < BME280_REPORT_SIZE {
            return Err(ErrorKind::InvalidInput);
        }

        let mut delay = Bme280Delay(KernelDelay);
        let measurements = self.sensor.lock().measure(&mut delay).map_err(|error| {
            log::warn!("Failed to measure BME280 data: {:?}", error);
            ErrorKind::Other
        })?;
        let mut report = [0u8; BME280_REPORT_SIZE];
        Self::encode_report(
            measurements.temperature,
            measurements.pressure,
            measurements.humidity,
            &mut report,
        );
        buf[..BME280_REPORT_SIZE].copy_from_slice(&report);
        Ok(BME280_REPORT_SIZE)
    }

    fn write(
        &self,
        _pos: u64,
        _buf: &[u8],
        _is_nonblocking: bool,
    ) -> core::result::Result<usize, ErrorKind> {
        Err(ErrorKind::Unsupported)
    }
}

impl Bme280Config {
    pub const fn new(device_addr: u8) -> Self {
        Bme280Config { device_addr }
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> InitDriver<BlockI2c<T>> for Bme280Config {
    type Data = ();
    fn init(self, bus: &Bus<BlockI2c<T>>) -> crate::drivers::Result<Self::Data> {
        let mut delay = Bme280Delay(KernelDelay);

        let mut bme280 = match self.device_addr {
            0x76 => BME280::new_primary(bus.intf.clone()),
            0x77 => BME280::new_secondary(bus.intf.clone()),
            _ => return Err(crate::error::code::EINVAL),
        };

        bme280
            .init(&mut delay)
            .map_err(|_| crate::error::code::EINVAL)?;

        let device = Arc::new(Bme280Device::<T>::new(bme280));
        DeviceManager::get()
            .register_device(String::from(BME280_DEVICE_NAME), device)
            .map_err(|_| crate::error::code::EIO)?;

        log::info!(
            "BME280 initialized successfully at address 0x{:X} as /dev/{}",
            self.device_addr,
            BME280_DEVICE_NAME
        );

        Ok(())
    }
}

pub struct Bme280DriverModule;

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> DriverModule<BlockI2c<T>> for Bme280DriverModule {
    type Data = Bme280Config;
    fn probe(dev: &crate::devices::DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }

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
