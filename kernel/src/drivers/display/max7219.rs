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

use alloc::{string::String, sync::Arc};
use blueos_driver::spi::SpiConfig;
use blueos_hal::{gpio::OutputPin, spi::Spi, PlatPeri};
use embedded_io::ErrorKind;
use max7219::{connectors::SpiConnector, MAX7219};

use crate::{
    devices::{
        bus::Bus,
        spi_core::{block_spi::BlockSpi, ExclusiveSpiWithCs},
        Device, DeviceClass, DeviceData, DeviceId, DeviceManager,
    },
    drivers::{DriverModule, InitDriver},
    sync::SpinLock,
};

pub const MAX7219_DEVICE_NAME: &str = "max7219";
const MAX7219_DEVICE_MAJOR: usize = 243;
const MAX7219_DEVICE_MINOR: usize = 0;
const MAX7219_DIGITS: usize = 8;
const MAX7219_MAX_DISPLAYS: usize = 8;
const MAX7219_MAX_INTENSITY: u8 = 0x0f;

type Max7219Spi<T, G> = MAX7219<SpiConnector<ExclusiveSpiWithCs<T, G>>>;

/// MAX7219 character device.
///
/// A write contains one or more consecutive 8-byte matrices. Each byte maps
/// to one digit/row and each bit controls one LED. Repeated writes always start
/// at the first display, which makes updating a frame through a character
/// device independent of the file position.
pub struct Max7219Device<T, G>
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    display: SpinLock<Max7219Spi<T, G>>,
    displays: usize,
}

impl<T, G> Max7219Device<T, G>
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    fn new(display: Max7219Spi<T, G>, displays: usize) -> Self {
        Self {
            display: SpinLock::new(display),
            displays,
        }
    }
}

impl<T, G> Device for Max7219Device<T, G>
where
    T: PlatPeri + Spi<SpiConfig, ()> + Sync,
    G: PlatPeri + OutputPin + Sync,
{
    fn name(&self) -> String {
        String::from(MAX7219_DEVICE_NAME)
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(MAX7219_DEVICE_MAJOR, MAX7219_DEVICE_MINOR)
    }

    fn read(
        &self,
        _pos: u64,
        _buf: &mut [u8],
        _is_nonblocking: bool,
    ) -> core::result::Result<usize, ErrorKind> {
        Err(ErrorKind::Unsupported)
    }

    fn write(
        &self,
        _pos: u64,
        buf: &[u8],
        _is_nonblocking: bool,
    ) -> core::result::Result<usize, ErrorKind> {
        if buf.is_empty()
            || buf.len() % MAX7219_DIGITS != 0
            || buf.len() > self.displays * MAX7219_DIGITS
        {
            return Err(ErrorKind::InvalidInput);
        }

        let mut display = self.display.lock();
        for (addr, raw) in buf.chunks_exact(MAX7219_DIGITS).enumerate() {
            let raw: &[u8; MAX7219_DIGITS] = raw.try_into().map_err(|_| ErrorKind::InvalidInput)?;
            display.write_raw(addr, raw).map_err(|error| {
                log::warn!("Failed to update MAX7219 display {}: {:?}", addr, error);
                ErrorKind::Other
            })?;
        }

        Ok(buf.len())
    }
}

pub struct Max7219Config<G: OutputPin> {
    pub cs: &'static G,
    pub displays: usize,
    pub intensity: u8,
}

impl<G: OutputPin> Max7219Config<G> {
    pub const fn new(cs: &'static G, displays: usize, intensity: u8) -> Self {
        Self {
            cs,
            displays,
            intensity,
        }
    }
}

impl<T, G> InitDriver<BlockSpi<T, G>> for Max7219Config<G>
where
    T: PlatPeri + Spi<SpiConfig, ()> + Sync,
    G: PlatPeri + OutputPin + Sync,
{
    type Data = ();

    fn init(self, bus: &Bus<BlockSpi<T, G>>) -> crate::drivers::Result<Self::Data> {
        if !(1..=MAX7219_MAX_DISPLAYS).contains(&self.displays)
            || self.intensity > MAX7219_MAX_INTENSITY
        {
            return Err(crate::error::code::EINVAL);
        }

        self.cs.set_high().map_err(|_| crate::error::code::EIO)?;
        let spi_device = ExclusiveSpiWithCs::new(bus.intf.clone(), self.cs);
        let mut display =
            MAX7219::from_spi(self.displays, spi_device).map_err(|_| crate::error::code::EIO)?;

        for addr in 0..self.displays {
            display
                .set_intensity(addr, self.intensity)
                .map_err(|_| crate::error::code::EIO)?;
        }
        display.power_on().map_err(|_| crate::error::code::EIO)?;

        let device = Arc::new(Max7219Device::<T, G>::new(display, self.displays));
        DeviceManager::get()
            .register_device(String::from(MAX7219_DEVICE_NAME), device)
            .map_err(|_| crate::error::code::EEXIST)?;

        log::info!(
            "MAX7219 initialized successfully with {} display(s), intensity {}, as /dev/{}",
            self.displays,
            self.intensity,
            MAX7219_DEVICE_NAME
        );
        Ok(())
    }
}

pub struct Max7219DriverModule<G> {
    _marker: core::marker::PhantomData<G>,
}

impl<G> Max7219DriverModule<G> {
    pub const fn new() -> Self {
        Self {
            _marker: core::marker::PhantomData,
        }
    }
}

impl<T, G> DriverModule<BlockSpi<T, G>> for Max7219DriverModule<G>
where
    T: PlatPeri + Spi<SpiConfig, ()> + Sync,
    G: PlatPeri + OutputPin + Sync,
{
    type Data = Max7219Config<G>;

    fn probe(dev: &DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }

                native_dev
                    .config::<Max7219Config<G>>()
                    .map(|config| Max7219Config::new(config.cs, config.displays, config.intensity))
                    .ok_or(crate::error::code::ENODEV)
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}
