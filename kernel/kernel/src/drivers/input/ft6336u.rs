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

use blueos_driver::i2c::I2cConfig;
use embedded_io::ErrorKind;
use ft6336u_driver::{TouchData, TouchStatus, FT6336U};

use crate::{
    devices::{
        bus::{Bus, BusWrapper},
        gpio::{GeneralGpio, Level},
        i2c_core::block_i2c::BlockI2c,
        Device, DeviceClass, DeviceData, DeviceId, DeviceManager,
    },
    drivers::{DriverModule, InitDriver, Result as DriverResult},
    sync::{KernelDelay, SpinLock},
};
use alloc::{string::String, sync::Arc};

const FT6336U_CHIP_ID: u8 = 0x64;
const RESET_LOW_MS: u32 = 10;
const STARTUP_DELAY_MS: u32 = 300;
const CHIP_ID_RETRIES: usize = 5;
const CHIP_ID_RETRY_DELAY_MS: u32 = 50;
const FT6336U_DEVICE_NAME: &str = "ft6336u0";
const FT6336U_DEVICE_MAJOR: usize = 240;
const FT6336U_DEVICE_MINOR: usize = 0;

/// Binary report returned by `/dev/ft6336u0`.
///
/// Layout (all 16-bit fields are little-endian):
/// - byte 0: format version (`1`)
/// - byte 1: active touch count (`0..=2`)
/// - bytes 2..=6: point 0 status, x, y
/// - bytes 7..=11: point 1 status, x, y
///
/// Status values are `0 = released`, `1 = new touch`, `2 = continuing touch`.
pub const FT6336U_REPORT_SIZE: usize = 12;
const FT6336U_REPORT_VERSION: u8 = 1;

pub struct Ft6336uDevice<T: blueos_hal::i2c::I2c<I2cConfig, ()>> {
    touch: SpinLock<FT6336U<BusWrapper<BlockI2c<T>>>>,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> Ft6336uDevice<T> {
    fn new(touch: FT6336U<BusWrapper<BlockI2c<T>>>) -> Self {
        Self {
            touch: SpinLock::new(touch),
        }
    }

    fn encode_report(data: TouchData, report: &mut [u8; FT6336U_REPORT_SIZE]) {
        report[0] = FT6336U_REPORT_VERSION;
        report[1] = data.touch_count.min(2);

        for (index, point) in data.points.iter().enumerate() {
            let offset = 2 + index * 5;
            report[offset] = match point.status {
                TouchStatus::Release => 0,
                TouchStatus::Touch => 1,
                TouchStatus::Stream => 2,
            };
            report[offset + 1..offset + 3].copy_from_slice(&point.x.to_le_bytes());
            report[offset + 3..offset + 5].copy_from_slice(&point.y.to_le_bytes());
        }
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> Device for Ft6336uDevice<T> {
    fn name(&self) -> String {
        String::from(FT6336U_DEVICE_NAME)
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(FT6336U_DEVICE_MAJOR, FT6336U_DEVICE_MINOR)
    }

    fn read(
        &self,
        _pos: u64,
        buf: &mut [u8],
        _is_nonblocking: bool,
    ) -> core::result::Result<usize, ErrorKind> {
        if buf.len() < FT6336U_REPORT_SIZE {
            return Err(ErrorKind::InvalidInput);
        }

        let data = self.touch.lock().scan().map_err(|error| {
            log::warn!("Failed to scan FT6336U touch data: {:?}", error);
            ErrorKind::Other
        })?;
        let mut report = [0u8; FT6336U_REPORT_SIZE];
        Self::encode_report(data, &mut report);
        buf[..FT6336U_REPORT_SIZE].copy_from_slice(&report);
        Ok(FT6336U_REPORT_SIZE)
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

pub struct Ft6336uConfig<G: blueos_hal::gpio::OutputPin> {
    pub rst: &'static G,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>, G: blueos_hal::gpio::OutputPin> InitDriver<BlockI2c<T>>
    for Ft6336uConfig<G>
{
    type Data = ();
    fn init(self, bus: &Bus<BlockI2c<T>>) -> DriverResult<Self::Data> {
        use embedded_hal::{delay::DelayNs, digital::OutputPin};

        let mut delay = KernelDelay;
        let mut rst = GeneralGpio::new(self.rst, Some(Level::Low));
        delay.delay_ms(RESET_LOW_MS);
        rst.set_high()?;
        delay.delay_ms(STARTUP_DELAY_MS);

        let mut touch = FT6336U::new(bus.intf.clone());
        let mut last_chip_id = None;
        for attempt in 0..CHIP_ID_RETRIES {
            match touch.read_chip_id() {
                Ok(FT6336U_CHIP_ID) => {
                    log::debug!("FT6336U chip ID: 0x{:X}", FT6336U_CHIP_ID);
                    let device = Arc::new(Ft6336uDevice::<T>::new(touch));
                    DeviceManager::get()
                        .register_device(String::from(FT6336U_DEVICE_NAME), device)
                        .map_err(|_| crate::error::code::EIO)?;
                    return Ok(());
                }
                Ok(id) => last_chip_id = Some(id),
                Err(error) if attempt + 1 == CHIP_ID_RETRIES => {
                    log::warn!("Failed to read FT6336U chip ID: {:?}", error);
                }
                Err(_) => {}
            }

            if attempt + 1 < CHIP_ID_RETRIES {
                delay.delay_ms(CHIP_ID_RETRY_DELAY_MS);
            }
        }

        log::warn!(
            "Unexpected FT6336U chip ID: {:?}, library version: {:?}, firmware ID: {:?}, FocalTech ID: {:?}",
            last_chip_id,
            touch.read_library_version(),
            touch.read_firmware_id(),
            touch.read_focaltech_id(),
        );
        Err(crate::error::code::EIO)
    }
}

pub struct Ft6336uDriverModule<G> {
    _marker: core::marker::PhantomData<G>,
}

impl<G> Ft6336uDriverModule<G> {
    pub const fn new() -> Self {
        Ft6336uDriverModule {
            _marker: core::marker::PhantomData,
        }
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>, G: blueos_hal::gpio::OutputPin>
    DriverModule<BlockI2c<T>> for Ft6336uDriverModule<G>
{
    type Data = Ft6336uConfig<G>;
    fn probe(dev: &crate::devices::DeviceData) -> DriverResult<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }

                if let Some(config) = native_dev.config::<Ft6336uConfig<G>>() {
                    Ok(Ft6336uConfig::<G> { rst: config.rst })
                } else {
                    Err(crate::error::code::ENODEV)
                }
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}
