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

use crate::{
    devices::{
        bus::Bus,
        gpio::{GeneralGpio, Level},
        spi_core::block_spi::BlockSpi,
        DeviceData,
    },
    drivers::{DriverModule, InitDriver},
    sync::KernelDelay,
};
use blueos_driver::spi::SpiConfig;
use blueos_hal::gpio::OutputPin;
use mipidsi::{interface::SpiInterface, models::ST7789, Builder};

pub struct St7789Config<G: blueos_hal::gpio::OutputPin> {
    pub rst: &'static G,
    pub dc: &'static G,
}

static mut BUFFER: [u8; 512] = [0; 512];
impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    InitDriver<BlockSpi<T, G>> for St7789Config<G>
{
    type Data = ();
    fn init(self, bus: &Bus<BlockSpi<T, G>>) -> crate::drivers::Result<Self::Data> {
        let mut delay = KernelDelay;

        let dc = GeneralGpio::new(self.dc, Some(Level::Low));
        let mut rst = GeneralGpio::new(self.rst, Some(Level::Low));
        use embedded_hal::digital::OutputPin;
        rst.set_high();

        let spi_device = bus.intf.clone();
        use mipidsi::options::ColorInversion;
        let di = SpiInterface::new(spi_device, dc, unsafe { &mut BUFFER });
        let mut display = Builder::new(ST7789, di)
            .reset_pin(rst)
            .invert_colors(ColorInversion::Inverted)
            .init(&mut delay)
            .map_err(|_| crate::error::code::EINVAL)?;

        log::debug!("ST7789 initialized successfully");

        Ok(())
    }
}

pub struct St7789DriverModule<G> {
    _marker: core::marker::PhantomData<G>,
}

impl<G> St7789DriverModule<G> {
    pub const fn new() -> Self {
        St7789DriverModule {
            _marker: core::marker::PhantomData,
        }
    }
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    DriverModule<BlockSpi<T, G>> for St7789DriverModule<G>
{
    type Data = St7789Config<G>;
    fn probe(dev: &crate::devices::DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }

                if let Some(config) = native_dev.config::<St7789Config<G>>() {
                    Ok(St7789Config::<G> {
                        rst: config.rst,
                        dc: config.dc,
                    })
                } else {
                    Err(crate::error::code::ENODEV)
                }
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}
