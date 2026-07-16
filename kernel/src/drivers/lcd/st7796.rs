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
        bus::{Bus, BusWrapper},
        gpio::{GeneralGpio, Level},
        spi_core::block_spi::BlockSpi,
        DeviceData,
    },
    drivers::{DriverModule, InitDriver},
    sync::KernelDelay,
};
use blueos_driver::spi::SpiConfig;
use blueos_hal::gpio::OutputPin;
use mipidsi::{
    interface::SpiInterface,
    models::{Model, ST7796},
    options::{ColorInversion, Orientation},
    Builder, Display,
};

pub struct St7796Config<G: blueos_hal::gpio::OutputPin> {
    pub rst: &'static G,
    pub dc: &'static G,
    pub orientation: Orientation,
}

static mut BUFFER: [u8; 512] = [0; 512];

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    InitDriver<BlockSpi<T, G>> for St7796Config<G>
{
    type Data = ();

    fn init(self, bus: &Bus<BlockSpi<T, G>>) -> crate::drivers::Result<Self::Data> {
        let mut delay = KernelDelay;

        let dc = GeneralGpio::new(self.dc, Some(Level::Low));
        let mut rst = GeneralGpio::new(self.rst, Some(Level::Low));
        use embedded_hal::digital::OutputPin;
        rst.set_high();

        let orientation = self.orientation;
        let spi_device = bus.intf.clone();
        let di = SpiInterface::new(spi_device, dc, unsafe { &mut BUFFER });
        let display = Builder::new(ST7796, di)
            .reset_pin(rst)
            .orientation(orientation)
            .invert_colors(ColorInversion::Inverted)
            .init(&mut delay)
            .map_err(|_| crate::error::code::EINVAL)?;
        let (width, height) = oriented_framebuffer_size(orientation);
        super::LcdFramebuffer::register_lcd(display, width, height)
            .map_err(|_| crate::error::code::EINVAL)?;
        log::debug!("ST7796 initialized successfully");

        Ok(())
    }
}

pub struct St7796DriverModule<G> {
    _marker: core::marker::PhantomData<G>,
}

impl<G> St7796DriverModule<G> {
    pub const fn new() -> Self {
        St7796DriverModule {
            _marker: core::marker::PhantomData,
        }
    }
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    DriverModule<BlockSpi<T, G>> for St7796DriverModule<G>
{
    type Data = St7796Config<G>;

    fn probe(dev: &crate::devices::DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }

                if let Some(config) = native_dev.config::<St7796Config<G>>() {
                    Ok(St7796Config::<G> {
                        rst: config.rst,
                        dc: config.dc,
                        orientation: config.orientation,
                    })
                } else {
                    Err(crate::error::code::ENODEV)
                }
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}

impl<
        G1: blueos_hal::gpio::OutputPin,
        G2: embedded_hal::digital::OutputPin + Send + 'static,
        T: blueos_hal::spi::Spi<SpiConfig, ()>,
    > super::Lcd
    for Display<SpiInterface<'static, BusWrapper<BlockSpi<T, G1>>, G2>, ST7796, GeneralGpio<G1>>
{
    fn draw_area(&mut self, area: super::DrawArea, color: &[u8]) -> Result<(), super::LcdError> {
        let area_width = area
            .col_end
            .checked_sub(area.col_start)
            .ok_or(super::LcdError::InvalidArea)?
            + 1;
        let area_height = area
            .row_end
            .checked_sub(area.row_start)
            .ok_or(super::LcdError::InvalidArea)?
            + 1;

        let (display_width, display_height) = oriented_framebuffer_size(self.orientation());
        if area.col_start >= display_width || area.row_start >= display_height {
            return Ok(());
        }

        let col_start = area.col_start;
        let row_start = area.row_start;
        let col_end = area.col_end.min(display_width - 1);
        let row_end = area.row_end.min(display_height - 1);
        let draw_width = col_end - col_start + 1;
        let draw_height = row_end - row_start + 1;
        let draw_pixels = draw_width
            .checked_mul(draw_height)
            .ok_or(super::LcdError::InvalidColorData)?;
        let area_pixels = area_width
            .checked_mul(area_height)
            .ok_or(super::LcdError::InvalidColorData)?;
        let expected_len = usize::try_from(area_pixels)
            .ok()
            .and_then(|count| count.checked_mul(super::LCD_BYTES_PER_PIXEL as usize))
            .ok_or(super::LcdError::InvalidColorData)?;
        if color.len() != expected_len {
            return Err(super::LcdError::InvalidColorData);
        }

        let initial_skip = (row_start - area.row_start) * area_width + (col_start - area.col_start);
        let skip_per_row = area_width - draw_width;
        let colors = Rgb565Pixels::new(color, initial_skip, draw_width, skip_per_row);

        self.set_pixels(
            col_start as u16,
            row_start as u16,
            col_end as u16,
            row_end as u16,
            colors.take(draw_pixels as usize),
        )
        .map_err(|_| super::LcdError::Bus)
    }
}

fn oriented_framebuffer_size(orientation: Orientation) -> (u32, u32) {
    let (width, height) = <ST7796 as Model>::FRAMEBUFFER_SIZE;
    if orientation.rotation.is_vertical() {
        (u32::from(height), u32::from(width))
    } else {
        (u32::from(width), u32::from(height))
    }
}

struct Rgb565Pixels<'a> {
    chunks: core::slice::ChunksExact<'a, u8>,
    take: u32,
    take_remaining: u32,
    skip: u32,
}

impl<'a> Rgb565Pixels<'a> {
    fn new(color: &'a [u8], initial_skip: u32, take: u32, skip: u32) -> Self {
        let mut chunks = color.chunks_exact(super::LCD_BYTES_PER_PIXEL as usize);
        if initial_skip > 0 {
            chunks.nth(initial_skip as usize - 1);
        }

        Self {
            chunks,
            take,
            take_remaining: take,
            skip,
        }
    }
}

impl Iterator for Rgb565Pixels<'_> {
    type Item = <ST7796 as Model>::ColorFormat;

    fn next(&mut self) -> Option<Self::Item> {
        let pixel = if self.take_remaining > 0 {
            self.take_remaining -= 1;
            self.chunks.next()
        } else if self.take > 0 {
            self.take_remaining = self.take - 1;
            self.chunks.nth(self.skip as usize)
        } else {
            None
        }?;

        let raw = u16::from_be_bytes([pixel[0], pixel[1]]);
        Some(<ST7796 as Model>::ColorFormat::new(
            ((raw >> 11) & 0x1f) as u8,
            ((raw >> 5) & 0x3f) as u8,
            (raw & 0x1f) as u8,
        ))
    }
}
