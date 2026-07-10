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

use core::sync::atomic::AtomicUsize;

use crate::devices::framebuffer::{
    FramebufferBitfield, FramebufferDevice, FramebufferFixedInfo, FramebufferOps,
    FramebufferVariableInfo,
};
use alloc::sync::Arc;
use spin::Mutex;

// FIXME: Only support 16-bit RGB565 format for now, need to support more formats in the future.
const LCD_BITS_PER_PIXEL: u32 = 16;
const LCD_BYTES_PER_PIXEL: u32 = LCD_BITS_PER_PIXEL / 8;
const FB_TYPE_PACKED_PIXELS: u32 = 0;
const FB_VISUAL_TRUECOLOR: u32 = 2;

#[cfg(st7789)]
pub mod st7789;

pub struct LcdFramebuffer<T> {
    width: u32,
    height: u32,
    display: Mutex<T>,
}

impl<T: Lcd> LcdFramebuffer<T> {
    fn line_length(&self) -> u32 {
        self.width * LCD_BYTES_PER_PIXEL
    }

    fn byte_len(&self) -> u32 {
        self.line_length() * self.height
    }

    fn register_lcd(lcd: T, width: u32, height: u32) -> Result<(), embedded_io::ErrorKind> {
        static INDEX: AtomicUsize = AtomicUsize::new(0);
        let fb = Arc::new(LcdFramebuffer::<T> {
            width,
            height,
            display: Mutex::new(lcd),
        });
        FramebufferDevice::register(INDEX.load(core::sync::atomic::Ordering::Relaxed), fb)?;
        INDEX.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
        Ok(())
    }
}

impl<T: Lcd> FramebufferOps for LcdFramebuffer<T> {
    fn fixed_info(&self) -> Result<FramebufferFixedInfo, embedded_io::ErrorKind> {
        let mut id = [0; 16];
        let id_bytes = b"blueos-lcd";
        for (dst, src) in id.iter_mut().zip(id_bytes.iter()) {
            *dst = *src as libc::c_char;
        }

        Ok(FramebufferFixedInfo {
            id,
            smem_len: self.byte_len(),
            type_: FB_TYPE_PACKED_PIXELS,
            visual: FB_VISUAL_TRUECOLOR,
            line_length: self.line_length(),
            ..FramebufferFixedInfo::default()
        })
    }

    fn variable_info(&self) -> Result<FramebufferVariableInfo, embedded_io::ErrorKind> {
        Ok(FramebufferVariableInfo {
            xres: self.width,
            yres: self.height,
            xres_virtual: self.width,
            yres_virtual: self.height,
            bits_per_pixel: LCD_BITS_PER_PIXEL,
            red: FramebufferBitfield {
                offset: 11,
                length: 5,
                msb_right: 0,
            },
            green: FramebufferBitfield {
                offset: 5,
                length: 6,
                msb_right: 0,
            },
            blue: FramebufferBitfield {
                offset: 0,
                length: 5,
                msb_right: 0,
            },
            ..FramebufferVariableInfo::default()
        })
    }

    fn set_variable_info(
        &self,
        variable_info: &crate::devices::framebuffer::FramebufferVariableInfo,
    ) -> Result<crate::devices::framebuffer::FramebufferVariableInfo, embedded_io::ErrorKind> {
        todo!()
    }

    fn read_bytes(&self, offset: u64, buf: &mut [u8]) -> Result<usize, embedded_io::ErrorKind> {
        todo!()
    }

    fn write_bytes(&self, offset: u64, buf: &[u8]) -> Result<usize, embedded_io::ErrorKind> {
        if offset % u64::from(LCD_BYTES_PER_PIXEL) != 0
            || buf.len() % LCD_BYTES_PER_PIXEL as usize != 0
        {
            return Err(embedded_io::ErrorKind::InvalidInput);
        }

        let mut pixel_index = u32::try_from(offset / u64::from(LCD_BYTES_PER_PIXEL))
            .map_err(|_| embedded_io::ErrorKind::InvalidInput)?;
        let mut written = 0;
        let mut display = self.display.lock();

        while written < buf.len() {
            let row = pixel_index / self.width;
            let col = pixel_index % self.width;
            let row_pixels =
                (self.width - col).min((buf.len() - written) as u32 / LCD_BYTES_PER_PIXEL);
            let row_bytes = row_pixels as usize * LCD_BYTES_PER_PIXEL as usize;
            display
                .draw_area(
                    DrawArea {
                        row_start: row,
                        row_end: row,
                        col_start: col,
                        col_end: col + row_pixels - 1,
                    },
                    &buf[written..written + row_bytes],
                )
                .map_err(lcd_error_to_io_error)?;
            pixel_index += row_pixels;
            written += row_bytes;
        }

        Ok(written)
    }

    fn byte_len(&self) -> Result<u64, embedded_io::ErrorKind> {
        Ok(u64::from(self.line_length()) * u64::from(self.height))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DrawArea {
    pub(super) row_start: u32,
    pub(super) row_end: u32,
    pub(super) col_start: u32,
    pub(super) col_end: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LcdError {
    InvalidArea,
    InvalidColorData,
    Bus,
}

fn lcd_error_to_io_error(error: LcdError) -> embedded_io::ErrorKind {
    match error {
        LcdError::InvalidArea | LcdError::InvalidColorData => embedded_io::ErrorKind::InvalidInput,
        LcdError::Bus => embedded_io::ErrorKind::Other,
    }
}

pub trait Lcd: Send + 'static {
    fn draw_area(&mut self, area: DrawArea, color: &[u8]) -> Result<(), LcdError>;
}
