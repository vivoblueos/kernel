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

use crate::devices::{Device, DeviceClass, DeviceId, DeviceManager};
use alloc::{format, string::String, sync::Arc, vec, vec::Vec};
use embedded_io::ErrorKind;
use libc::{FBIOGET_FSCREENINFO, FBIOGET_VSCREENINFO, FBIOPUT_VSCREENINFO};
use spin::Mutex;

/// Linux framebuffer character-device major number.
pub const FRAMEBUFFER_MAJOR: usize = 29;

/// Kernel representation of Linux `struct fb_bitfield`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct FramebufferBitfield {
    /// Bit offset from the right.
    pub offset: u32,
    /// Bitfield length in bits.
    pub length: u32,
    /// Non-zero when the most significant bit is on the right.
    pub msb_right: u32,
}

/// Kernel representation of Linux `struct fb_fix_screeninfo`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct FramebufferFixedInfo {
    /// Identification string.
    pub id: [libc::c_char; 16],
    /// Start of framebuffer memory, represented as BlueOS `c_ulong` (`u32`).
    pub smem_start: u32,
    /// Framebuffer memory length in bytes.
    pub smem_len: u32,
    /// Framebuffer type.
    pub type_: u32,
    /// Interleave information for interleaved planes.
    pub type_aux: u32,
    /// Visual type.
    pub visual: u32,
    /// Zero when horizontal panning is unsupported.
    pub xpanstep: u16,
    /// Zero when vertical panning is unsupported.
    pub ypanstep: u16,
    /// Zero when vertical wrapping is unsupported.
    pub ywrapstep: u16,
    /// Bytes per line.
    pub line_length: u32,
    /// Start of memory-mapped I/O, represented as BlueOS `c_ulong` (`u32`).
    pub mmio_start: u32,
    /// Memory-mapped I/O length in bytes.
    pub mmio_len: u32,
    /// Accelerator identifier.
    pub accel: u32,
    /// Driver capabilities.
    pub capabilities: u16,
    /// Reserved for ABI compatibility.
    pub reserved: [u16; 2],
    /// Tail padding reserved for ABI compatibility.
    pub reserved_tail: [u8; 12],
}

/// Kernel representation of Linux `struct fb_var_screeninfo`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct FramebufferVariableInfo {
    /// Visible horizontal resolution in pixels.
    pub xres: u32,
    /// Visible vertical resolution in pixels.
    pub yres: u32,
    /// Virtual horizontal resolution in pixels.
    pub xres_virtual: u32,
    /// Virtual vertical resolution in pixels.
    pub yres_virtual: u32,
    /// Horizontal offset from virtual to visible resolution.
    pub xoffset: u32,
    /// Vertical offset from virtual to visible resolution.
    pub yoffset: u32,
    /// Pixel depth in bits.
    pub bits_per_pixel: u32,
    /// Grayscale mode.
    pub grayscale: u32,
    /// Red component bitfield.
    pub red: FramebufferBitfield,
    /// Green component bitfield.
    pub green: FramebufferBitfield,
    /// Blue component bitfield.
    pub blue: FramebufferBitfield,
    /// Transparency component bitfield.
    pub transp: FramebufferBitfield,
    /// Non-standard pixel format marker.
    pub nonstd: u32,
    /// Activation flags.
    pub activate: u32,
    /// Physical screen height in millimeters.
    pub height: u32,
    /// Physical screen width in millimeters.
    pub width: u32,
    /// Acceleration flags.
    pub accel_flags: u32,
    /// Pixel clock in picoseconds.
    pub pixclock: u32,
    /// Left margin in pixels.
    pub left_margin: u32,
    /// Right margin in pixels.
    pub right_margin: u32,
    /// Upper margin in pixels.
    pub upper_margin: u32,
    /// Lower margin in pixels.
    pub lower_margin: u32,
    /// Horizontal sync length in pixels.
    pub hsync_len: u32,
    /// Vertical sync length in pixels.
    pub vsync_len: u32,
    /// Sync flags.
    pub sync: u32,
    /// Video mode flags.
    pub vmode: u32,
    /// Rotation angle.
    pub rotate: u32,
    /// Color space identifier.
    pub colorspace: u32,
    /// Reserved for ABI compatibility.
    pub reserved: [u32; 4],
}

const _: [(); 12] = [(); core::mem::size_of::<FramebufferBitfield>()];
const _: [(); 80] = [(); core::mem::size_of::<FramebufferFixedInfo>()];
const _: [(); 160] = [(); core::mem::size_of::<FramebufferVariableInfo>()];

unsafe fn load_user_variable_info(
    ptr: *const FramebufferVariableInfo,
) -> Result<FramebufferVariableInfo, ErrorKind> {
    if ptr.is_null() {
        return Err(ErrorKind::InvalidInput);
    }
    Ok(*ptr)
}

unsafe fn store_user_fixed_info(
    ptr: *mut FramebufferFixedInfo,
    fixed_info: &FramebufferFixedInfo,
) -> Result<(), ErrorKind> {
    if ptr.is_null() {
        return Err(ErrorKind::InvalidInput);
    }
    *ptr = *fixed_info;
    Ok(())
}

unsafe fn store_user_variable_info(
    ptr: *mut FramebufferVariableInfo,
    variable_info: &FramebufferVariableInfo,
) -> Result<(), ErrorKind> {
    if ptr.is_null() {
        return Err(ErrorKind::InvalidInput);
    }
    *ptr = *variable_info;
    Ok(())
}

/// Driver-facing framebuffer operations.
pub trait FramebufferOps: Send + Sync {
    /// Return fixed framebuffer metadata.
    fn fixed_info(&self) -> Result<FramebufferFixedInfo, ErrorKind>;

    /// Return variable framebuffer metadata.
    fn variable_info(&self) -> Result<FramebufferVariableInfo, ErrorKind>;

    /// Validate and apply a variable-info update, returning the effective state.
    fn set_variable_info(
        &self,
        variable_info: &FramebufferVariableInfo,
    ) -> Result<FramebufferVariableInfo, ErrorKind>;

    /// Read framebuffer bytes starting at `offset`.
    fn read_bytes(&self, offset: u64, buf: &mut [u8]) -> Result<usize, ErrorKind>;

    /// Write framebuffer bytes starting at `offset`.
    fn write_bytes(&self, offset: u64, buf: &[u8]) -> Result<usize, ErrorKind>;

    /// Return the framebuffer byte length.
    fn byte_len(&self) -> Result<u64, ErrorKind>;
}

const MEMORY_FB_WIDTH: u32 = 16;
const MEMORY_FB_HEIGHT: u32 = 16;
const MEMORY_FB_BPP: u32 = 32;
const MEMORY_FB_BYTES_PER_PIXEL: u32 = MEMORY_FB_BPP / 8;
const MEMORY_FB_LINE_LENGTH: u32 = MEMORY_FB_WIDTH * MEMORY_FB_BYTES_PER_PIXEL;
const MEMORY_FB_BYTE_LEN: usize = (MEMORY_FB_LINE_LENGTH * MEMORY_FB_HEIGHT) as usize;
const FB_TYPE_PACKED_PIXELS: u32 = 0;
const FB_VISUAL_TRUECOLOR: u32 = 2;

/// Memory-backed framebuffer for tests and early bring-up.
pub struct MemoryFramebuffer {
    fixed_info: FramebufferFixedInfo,
    variable_info: FramebufferVariableInfo,
    data: Mutex<Vec<u8>>,
}

impl MemoryFramebuffer {
    /// Create a deterministic 16x16 ARGB8888 memory framebuffer.
    #[must_use]
    pub fn new() -> Self {
        Self {
            fixed_info: memory_fixed_info(),
            variable_info: memory_variable_info(),
            data: Mutex::new(vec![0; MEMORY_FB_BYTE_LEN]),
        }
    }
}

impl Default for MemoryFramebuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl FramebufferOps for MemoryFramebuffer {
    fn fixed_info(&self) -> Result<FramebufferFixedInfo, ErrorKind> {
        Ok(self.fixed_info)
    }

    fn variable_info(&self) -> Result<FramebufferVariableInfo, ErrorKind> {
        Ok(self.variable_info)
    }

    fn set_variable_info(
        &self,
        variable_info: &FramebufferVariableInfo,
    ) -> Result<FramebufferVariableInfo, ErrorKind> {
        if *variable_info == self.variable_info {
            Ok(self.variable_info)
        } else {
            Err(ErrorKind::InvalidInput)
        }
    }

    fn read_bytes(&self, offset: u64, buf: &mut [u8]) -> Result<usize, ErrorKind> {
        let offset = usize::try_from(offset).map_err(|_| ErrorKind::InvalidInput)?;
        let data = self.data.lock();
        if offset >= data.len() {
            return Ok(0);
        }
        let read_len = buf.len().min(data.len() - offset);
        buf[..read_len].copy_from_slice(&data[offset..offset + read_len]);
        Ok(read_len)
    }

    fn write_bytes(&self, offset: u64, buf: &[u8]) -> Result<usize, ErrorKind> {
        let offset = usize::try_from(offset).map_err(|_| ErrorKind::InvalidInput)?;
        let mut data = self.data.lock();
        if offset >= data.len() {
            return Ok(0);
        }
        let write_len = buf.len().min(data.len() - offset);
        data[offset..offset + write_len].copy_from_slice(&buf[..write_len]);
        Ok(write_len)
    }

    fn byte_len(&self) -> Result<u64, ErrorKind> {
        Ok(MEMORY_FB_BYTE_LEN as u64)
    }
}

fn memory_fixed_info() -> FramebufferFixedInfo {
    let mut id = [0; 16];
    let id_bytes = b"blueos-memfb";
    for (dst, src) in id.iter_mut().zip(id_bytes.iter()) {
        *dst = *src as libc::c_char;
    }

    FramebufferFixedInfo {
        id,
        smem_len: MEMORY_FB_BYTE_LEN as u32,
        type_: FB_TYPE_PACKED_PIXELS,
        visual: FB_VISUAL_TRUECOLOR,
        line_length: MEMORY_FB_LINE_LENGTH,
        ..FramebufferFixedInfo::default()
    }
}

fn memory_variable_info() -> FramebufferVariableInfo {
    FramebufferVariableInfo {
        xres: MEMORY_FB_WIDTH,
        yres: MEMORY_FB_HEIGHT,
        xres_virtual: MEMORY_FB_WIDTH,
        yres_virtual: MEMORY_FB_HEIGHT,
        bits_per_pixel: MEMORY_FB_BPP,
        red: FramebufferBitfield {
            offset: 16,
            length: 8,
            msb_right: 0,
        },
        green: FramebufferBitfield {
            offset: 8,
            length: 8,
            msb_right: 0,
        },
        blue: FramebufferBitfield {
            offset: 0,
            length: 8,
            msb_right: 0,
        },
        transp: FramebufferBitfield {
            offset: 24,
            length: 8,
            msb_right: 0,
        },
        ..FramebufferVariableInfo::default()
    }
}

/// Register the initial memory-backed framebuffer.
pub fn init() -> Result<(), ErrorKind> {
    FramebufferDevice::register(0, Arc::new(MemoryFramebuffer::new()))
}

/// Character-device wrapper for a framebuffer implementation.
pub struct FramebufferDevice {
    name: String,
    id: DeviceId,
    ops: Arc<dyn FramebufferOps>,
}

impl FramebufferDevice {
    /// Create a framebuffer device named `fb{index}` with Linux framebuffer major `29`.
    #[must_use]
    pub fn new(index: usize, ops: Arc<dyn FramebufferOps>) -> Self {
        Self::with_id(
            format!("fb{index}"),
            DeviceId::new(FRAMEBUFFER_MAJOR, index),
            ops,
        )
    }

    /// Create a framebuffer device with an explicit name and device id.
    #[must_use]
    pub fn with_id(name: String, id: DeviceId, ops: Arc<dyn FramebufferOps>) -> Self {
        Self { name, id, ops }
    }

    /// Register a framebuffer device named `fb{index}`.
    pub fn register(index: usize, ops: Arc<dyn FramebufferOps>) -> Result<(), ErrorKind> {
        Self::register_device(Arc::new(Self::new(index, ops)))
    }

    /// Register an already constructed framebuffer device.
    pub fn register_device(device: Arc<Self>) -> Result<(), ErrorKind> {
        let name = device.name.clone();
        DeviceManager::get().register_device(name, device)
    }

    /// Return the device name.
    #[must_use]
    pub fn device_name(&self) -> &str {
        &self.name
    }

    /// Return the device identifier.
    #[must_use]
    pub const fn device_id(&self) -> DeviceId {
        self.id
    }

    /// Return fixed framebuffer metadata.
    pub fn fixed_info(&self) -> Result<FramebufferFixedInfo, ErrorKind> {
        self.ops.fixed_info()
    }

    /// Return variable framebuffer metadata.
    pub fn variable_info(&self) -> Result<FramebufferVariableInfo, ErrorKind> {
        self.ops.variable_info()
    }

    /// Validate and apply a variable-info update, returning the effective state.
    pub fn set_variable_info(
        &self,
        variable_info: &FramebufferVariableInfo,
    ) -> Result<FramebufferVariableInfo, ErrorKind> {
        self.ops.set_variable_info(variable_info)
    }
}

impl Device for FramebufferDevice {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        self.id
    }

    fn read(&self, pos: u64, buf: &mut [u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        if buf.is_empty() {
            return Ok(0);
        }

        let byte_len = self.ops.byte_len()?;
        if pos >= byte_len {
            return Ok(0);
        }

        let remaining = byte_len - pos;
        let read_len =
            usize::try_from(remaining).map_or(buf.len(), |remaining| remaining.min(buf.len()));
        self.ops.read_bytes(pos, &mut buf[..read_len])
    }

    fn write(&self, pos: u64, buf: &[u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        if buf.is_empty() {
            return Ok(0);
        }

        let byte_len = self.ops.byte_len()?;
        if pos >= byte_len {
            return Ok(0);
        }

        let remaining = byte_len - pos;
        let write_len =
            usize::try_from(remaining).map_or(buf.len(), |remaining| remaining.min(buf.len()));
        self.ops.write_bytes(pos, &buf[..write_len])
    }

    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        match request {
            req if req == FBIOGET_FSCREENINFO => {
                let fixed_info = self.ops.fixed_info()?;
                unsafe { store_user_fixed_info(arg as *mut FramebufferFixedInfo, &fixed_info) }
            }
            req if req == FBIOGET_VSCREENINFO => {
                let variable_info = self.ops.variable_info()?;
                unsafe {
                    store_user_variable_info(arg as *mut FramebufferVariableInfo, &variable_info)
                }
            }
            req if req == FBIOPUT_VSCREENINFO => {
                let requested_info =
                    unsafe { load_user_variable_info(arg as *const FramebufferVariableInfo)? };
                let effective_info = self.ops.set_variable_info(&requested_info)?;
                unsafe {
                    store_user_variable_info(arg as *mut FramebufferVariableInfo, &effective_info)
                }
            }
            _ => Err(ErrorKind::InvalidData),
        }
    }

    fn capacity(&self) -> Result<u64, ErrorKind> {
        self.ops.byte_len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    fn test_device() -> FramebufferDevice {
        FramebufferDevice::new(0, Arc::new(MemoryFramebuffer::new()))
    }

    #[test]
    fn test_framebuffer_device_identity() {
        let device = test_device();

        assert_eq!(device.device_name(), "fb0");
        assert_eq!(device.class(), DeviceClass::Char);
        assert_eq!(device.device_id().major(), FRAMEBUFFER_MAJOR);
        assert_eq!(device.device_id().minor(), 0);
    }

    #[test]
    fn test_memory_framebuffer_read_write_bounds_and_capacity() {
        let device = test_device();
        let capacity = device.capacity().unwrap();
        assert_eq!(capacity, MEMORY_FB_BYTE_LEN as u64);

        let written = device.write(2, &[1, 2, 3, 4], false).unwrap();
        assert_eq!(written, 4);

        let mut read_buf = [0; 4];
        let read = device.read(2, &mut read_buf, false).unwrap();
        assert_eq!(read, 4);
        assert_eq!(read_buf, [1, 2, 3, 4]);

        let tail = [9; 8];
        let written = device.write(capacity - 2, &tail, false).unwrap();
        assert_eq!(written, 2);

        let mut tail_read = [0; 8];
        let read = device.read(capacity - 2, &mut tail_read, false).unwrap();
        assert_eq!(read, 2);
        assert_eq!(&tail_read[..2], &[9, 9]);

        assert_eq!(device.read(capacity, &mut tail_read, false).unwrap(), 0);
        assert_eq!(device.write(capacity, &tail, false).unwrap(), 0);
    }

    #[test]
    fn test_memory_framebuffer_ioctl_get_and_put_success() {
        let device = test_device();

        let mut fixed_info = FramebufferFixedInfo::default();
        assert_eq!(
            device.ioctl(FBIOGET_FSCREENINFO, (&mut fixed_info as *mut _) as usize),
            Ok(())
        );
        assert_eq!(fixed_info.smem_len, MEMORY_FB_BYTE_LEN as u32);
        assert_eq!(fixed_info.line_length, MEMORY_FB_LINE_LENGTH);

        let mut variable_info = FramebufferVariableInfo::default();
        assert_eq!(
            device.ioctl(FBIOGET_VSCREENINFO, (&mut variable_info as *mut _) as usize),
            Ok(())
        );
        assert_eq!(variable_info.xres, MEMORY_FB_WIDTH);
        assert_eq!(variable_info.yres, MEMORY_FB_HEIGHT);
        assert_eq!(variable_info.bits_per_pixel, MEMORY_FB_BPP);

        assert_eq!(
            device.ioctl(FBIOPUT_VSCREENINFO, (&mut variable_info as *mut _) as usize),
            Ok(())
        );
        assert_eq!(variable_info, memory_variable_info());
    }

    #[test]
    fn test_memory_framebuffer_ioctl_put_unsupported_update() {
        let device = test_device();
        let mut variable_info = memory_variable_info();
        variable_info.xres += 1;

        assert_eq!(
            device.ioctl(FBIOPUT_VSCREENINFO, (&mut variable_info as *mut _) as usize),
            Err(ErrorKind::InvalidInput)
        );
    }

    #[test]
    fn test_framebuffer_ioctl_errors() {
        let device = test_device();

        assert_eq!(
            device.ioctl(
                FBIOGET_FSCREENINFO,
                core::ptr::null_mut::<FramebufferFixedInfo>() as usize
            ),
            Err(ErrorKind::InvalidInput)
        );
        assert_eq!(
            device.ioctl(
                FBIOGET_VSCREENINFO,
                core::ptr::null_mut::<FramebufferVariableInfo>() as usize
            ),
            Err(ErrorKind::InvalidInput)
        );
        assert_eq!(
            device.ioctl(
                FBIOPUT_VSCREENINFO,
                core::ptr::null_mut::<FramebufferVariableInfo>() as usize
            ),
            Err(ErrorKind::InvalidInput)
        );
        assert_eq!(device.ioctl(0xffff_ffff, 0), Err(ErrorKind::InvalidData));
    }
}
