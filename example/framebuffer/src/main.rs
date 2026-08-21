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

extern crate embedded_graphics;
extern crate librs;
extern crate rsrt;

use embedded_graphics::{
    prelude::*,
    primitives::{PrimitiveStyle, Rectangle},
};
use embedded_graphics_core::{
    draw_target::DrawTarget,
    geometry::OriginDimensions,
    pixelcolor::{raw::ToBytes, Rgb565, RgbColor},
    Pixel,
};
use librs::{c_str::CStr, syscall::Syscall};
use std::io::{Error, ErrorKind, Result};

#[derive(Clone, Copy)]
enum PixelFormat {
    Rgb565,
    Bgra8888,
}

impl PixelFormat {
    fn bytes_per_pixel(self) -> u32 {
        match self {
            Self::Rgb565 => 2,
            Self::Bgra8888 => 4,
        }
    }
}

struct FbFile {
    fd: libc::c_int,
    fixed_info: libc::fb_fix_screeninfo,
    variable_info: libc::fb_var_screeninfo,
    pixel_format: PixelFormat,
}

impl FbFile {
    fn open() -> Result<Self> {
        let path = CStr::from_bytes_with_nul(b"/dev/fb0\0")
            .map_err(|_| Error::from_raw_os_error(libc::EINVAL))?;
        let fd = librs::syscall::sys::Sys::open(path, libc::O_RDWR, 0);
        if fd < 0 {
            return Err(syscall_error(fd));
        }

        let mut fb = Self {
            fd,
            fixed_info: unsafe { core::mem::zeroed() },
            variable_info: unsafe { core::mem::zeroed() },
            pixel_format: PixelFormat::Rgb565,
        };

        if let Err(err) = fb.load_info().and_then(|_| fb.validate_format()) {
            let _ = librs::syscall::sys::Sys::close(fd);
            return Err(err);
        }

        fb.print_info();
        Ok(fb)
    }

    fn print_info(&self) {
        let fixed = &self.fixed_info;
        let variable = &self.variable_info;

        println!("FBIOGET_FSCREENINFO:");
        println!("  id: {}", fb_id_to_str(&fixed.id));
        println!("  smem_start: {:#x}", fixed.smem_start);
        println!("  smem_len: {}", fixed.smem_len);
        println!("  type: {}", fixed.type_);
        println!("  type_aux: {}", fixed.type_aux);
        println!("  visual: {}", fixed.visual);
        println!("  xpanstep: {}", fixed.xpanstep);
        println!("  ypanstep: {}", fixed.ypanstep);
        println!("  ywrapstep: {}", fixed.ywrapstep);
        println!("  line_length: {}", fixed.line_length);
        println!("  mmio_start: {:#x}", fixed.mmio_start);
        println!("  mmio_len: {}", fixed.mmio_len);
        println!("  accel: {}", fixed.accel);
        println!("  capabilities: {}", fixed.capabilities);

        println!("FBIOGET_VSCREENINFO:");
        println!("  xres: {}", variable.xres);
        println!("  yres: {}", variable.yres);
        println!("  xres_virtual: {}", variable.xres_virtual);
        println!("  yres_virtual: {}", variable.yres_virtual);
        println!("  xoffset: {}", variable.xoffset);
        println!("  yoffset: {}", variable.yoffset);
        println!("  bits_per_pixel: {}", variable.bits_per_pixel);
        println!("  grayscale: {}", variable.grayscale);
        print_bitfield("red", &variable.red);
        print_bitfield("green", &variable.green);
        print_bitfield("blue", &variable.blue);
        print_bitfield("transp", &variable.transp);
        println!("  nonstd: {}", variable.nonstd);
        println!("  activate: {}", variable.activate);
        println!("  height: {}", variable.height);
        println!("  width: {}", variable.width);
        println!("  accel_flags: {}", variable.accel_flags);
        println!("  pixclock: {}", variable.pixclock);
        println!("  left_margin: {}", variable.left_margin);
        println!("  right_margin: {}", variable.right_margin);
        println!("  upper_margin: {}", variable.upper_margin);
        println!("  lower_margin: {}", variable.lower_margin);
        println!("  hsync_len: {}", variable.hsync_len);
        println!("  vsync_len: {}", variable.vsync_len);
        println!("  sync: {}", variable.sync);
        println!("  vmode: {}", variable.vmode);
        println!("  rotate: {}", variable.rotate);
        println!("  colorspace: {}", variable.colorspace);
    }

    fn load_info(&mut self) -> Result<()> {
        unsafe {
            ioctl(
                self.fd,
                libc::FBIOGET_FSCREENINFO,
                &mut self.fixed_info as *mut libc::fb_fix_screeninfo as *mut libc::c_void,
            )?;
            ioctl(
                self.fd,
                libc::FBIOGET_VSCREENINFO,
                &mut self.variable_info as *mut libc::fb_var_screeninfo as *mut libc::c_void,
            )?;
        }
        Ok(())
    }

    fn validate_format(&mut self) -> Result<()> {
        let info = &self.variable_info;
        let fixed = &self.fixed_info;
        let pixel_format = if is_rgb565(info) {
            PixelFormat::Rgb565
        } else if is_bgra8888(info) {
            PixelFormat::Bgra8888
        } else {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "unsupported framebuffer format",
            ));
        };
        let min_line_length = info
            .xres
            .checked_mul(pixel_format.bytes_per_pixel())
            .ok_or_else(|| Error::from_raw_os_error(libc::EINVAL))?;
        let min_size = fixed
            .line_length
            .checked_mul(info.yres)
            .ok_or_else(|| Error::from_raw_os_error(libc::EINVAL))?;

        if fixed.line_length < min_line_length || fixed.smem_len < min_size {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "unsupported framebuffer format",
            ));
        }

        self.pixel_format = pixel_format;
        Ok(())
    }

    fn draw_pixel(&mut self, x: u32, y: u32, color: Rgb565) -> Result<()> {
        let offset = y as u64 * self.fixed_info.line_length as u64
            + x as u64 * self.pixel_format.bytes_per_pixel() as u64;
        if offset > libc::off_t::MAX as u64 {
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }

        let offset =
            librs::syscall::sys::Sys::lseek(self.fd, offset as libc::off_t, libc::SEEK_SET);
        if offset < 0 {
            return Err(syscall_error(offset as libc::c_int));
        }

        match self.pixel_format {
            PixelFormat::Rgb565 => write_all(self.fd, &color.to_be_bytes()),
            PixelFormat::Bgra8888 => write_all(self.fd, &rgb565_to_bgra8888(color)),
        }
    }
}

impl Drop for FbFile {
    fn drop(&mut self) {
        let _ = librs::syscall::sys::Sys::close(self.fd);
    }
}

impl OriginDimensions for FbFile {
    fn size(&self) -> Size {
        Size::new(self.variable_info.xres, self.variable_info.yres)
    }
}

impl DrawTarget for FbFile {
    type Error = Error;
    type Color = Rgb565;

    fn draw_iter<I>(&mut self, pixels: I) -> Result<()>
    where
        I: IntoIterator<Item = Pixel<Self::Color>>,
    {
        for Pixel(point, color) in pixels {
            if point.x < 0 || point.y < 0 {
                continue;
            }

            let x = point.x as u32;
            let y = point.y as u32;
            if x >= self.variable_info.xres || y >= self.variable_info.yres {
                continue;
            }

            self.draw_pixel(x, y, color)?;
        }

        Ok(())
    }
}

unsafe fn ioctl(fd: libc::c_int, request: libc::c_ulong, arg: *mut libc::c_void) -> Result<()> {
    match librs::syscall::sys::Sys::ioctl(fd, request, arg) {
        Ok(ret) if ret < 0 => Err(syscall_error(ret)),
        Ok(_) => Ok(()),
        Err(librs::errno::Errno(errno)) => Err(Error::from_raw_os_error(errno)),
    }
}

fn write_all(fd: libc::c_int, mut buf: &[u8]) -> Result<()> {
    while !buf.is_empty() {
        match librs::syscall::sys::Sys::write(fd, buf) {
            Ok(0) => {
                return Err(Error::new(
                    ErrorKind::WriteZero,
                    "failed to write framebuffer",
                ));
            }
            Ok(size) => buf = &buf[size..],
            Err(librs::errno::Errno(errno)) => return Err(Error::from_raw_os_error(errno)),
        }
    }

    Ok(())
}

fn fb_id_to_str(id: &[libc::c_char; 16]) -> &str {
    let len = id.iter().position(|&ch| ch == 0).unwrap_or(id.len());
    let bytes = unsafe { core::slice::from_raw_parts(id.as_ptr() as *const u8, len) };

    core::str::from_utf8(bytes).unwrap_or("<invalid utf8>")
}

fn print_bitfield(name: &str, bitfield: &libc::fb_bitfield) {
    println!(
        "  {name}: offset={}, length={}, msb_right={}",
        bitfield.offset, bitfield.length, bitfield.msb_right
    );
}

fn is_rgb565(info: &libc::fb_var_screeninfo) -> bool {
    info.bits_per_pixel == 16
        && info.red.offset == 11
        && info.red.length == 5
        && info.green.offset == 5
        && info.green.length == 6
        && info.blue.offset == 0
        && info.blue.length == 5
}

fn is_bgra8888(info: &libc::fb_var_screeninfo) -> bool {
    info.bits_per_pixel == 32
        && info.red.offset == 16
        && info.red.length == 8
        && info.green.offset == 8
        && info.green.length == 8
        && info.blue.offset == 0
        && info.blue.length == 8
}

fn rgb565_to_bgra8888(color: Rgb565) -> [u8; 4] {
    [color.b(), color.g(), color.r(), 0xff]
}

fn syscall_error(ret: libc::c_int) -> Error {
    if ret == -1 {
        Error::last_os_error()
    } else {
        Error::from_raw_os_error(-ret)
    }
}

const CELL_SIZE: u32 = 8;
const FRAME_DELAY_MS: libc::c_uint = 80;
const INITIAL_SNAKE_LEN: usize = 5;
const MAX_SNAKE_LEN: usize = 48;

#[derive(Clone, Copy)]
struct Cell {
    x: i32,
    y: i32,
}

fn draw_cell(fb: &mut FbFile, cell: Cell, color: Rgb565) -> Result<()> {
    Rectangle::new(
        Point::new(cell.x * CELL_SIZE as i32, cell.y * CELL_SIZE as i32),
        Size::new(CELL_SIZE, CELL_SIZE),
    )
    .into_styled(PrimitiveStyle::with_fill(color))
    .draw(fb)
}

fn loop_path_len(grid_width: usize, grid_height: usize) -> usize {
    grid_width * 2 + grid_height * 2 - 4
}

fn loop_cell(index: usize, grid_width: usize, grid_height: usize) -> Cell {
    let right = grid_width - 1;
    let bottom = grid_height - 1;

    if index < grid_width {
        Cell {
            x: index as i32,
            y: 0,
        }
    } else if index < grid_width + bottom {
        Cell {
            x: right as i32,
            y: (index - grid_width + 1) as i32,
        }
    } else if index < grid_width + bottom + right {
        Cell {
            x: (right - (index - grid_width - bottom + 1)) as i32,
            y: bottom as i32,
        }
    } else {
        Cell {
            x: 0,
            y: (bottom - (index - grid_width - bottom - right + 1)) as i32,
        }
    }
}

fn snake_contains(index: usize, head_index: usize, length: usize, path_len: usize) -> bool {
    (0..length).any(|offset| (head_index + path_len - offset) % path_len == index)
}

fn next_food_index(head_index: usize, length: usize, path_len: usize, seed: usize) -> usize {
    for offset in 1..path_len {
        let index = (head_index + seed * 11 + offset) % path_len;
        if !snake_contains(index, head_index, length, path_len) {
            return index;
        }
    }

    head_index
}

fn run_snake(fb: &mut FbFile) -> Result<()> {
    let size = fb.size();
    let grid_width = (size.width / CELL_SIZE) as usize;
    let grid_height = (size.height / CELL_SIZE) as usize;
    if grid_width < 2 || grid_height < 2 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "framebuffer is too small for snake",
        ));
    }

    let path_len = loop_path_len(grid_width, grid_height);
    let max_len = MAX_SNAKE_LEN.min(path_len - 1);
    let mut length = INITIAL_SNAKE_LEN.min(max_len);
    let mut head_index = length - 1;
    let mut food_seed = 1;
    let mut food_index = next_food_index(head_index, length, path_len, food_seed);

    fb.clear(Rgb565::BLACK)?;
    draw_cell(
        fb,
        loop_cell(food_index, grid_width, grid_height),
        Rgb565::RED,
    )?;
    for offset in (0..length).rev() {
        let index = (head_index + path_len - offset) % path_len;
        let color = if offset == 0 {
            Rgb565::YELLOW
        } else {
            Rgb565::GREEN
        };
        draw_cell(fb, loop_cell(index, grid_width, grid_height), color)?;
    }

    loop {
        let _ = librs::time::msleep(FRAME_DELAY_MS);

        let old_head_index = head_index;
        let old_tail_index = (head_index + path_len - length + 1) % path_len;
        head_index = (head_index + 1) % path_len;

        let ate_food = head_index == food_index;
        if ate_food && length < max_len {
            length += 1;
        } else {
            draw_cell(
                fb,
                loop_cell(old_tail_index, grid_width, grid_height),
                Rgb565::BLACK,
            )?;
        }

        draw_cell(
            fb,
            loop_cell(old_head_index, grid_width, grid_height),
            Rgb565::GREEN,
        )?;
        draw_cell(
            fb,
            loop_cell(head_index, grid_width, grid_height),
            Rgb565::YELLOW,
        )?;

        if ate_food {
            food_seed += 1;
            food_index = next_food_index(head_index, length, path_len, food_seed);
            draw_cell(
                fb,
                loop_cell(food_index, grid_width, grid_height),
                Rgb565::RED,
            )?;
        }
    }
}

fn main() -> Result<()> {
    println!("Framebuffer example application started");
    let mut fb = FbFile::open()?;

    run_snake(&mut fb)
}
