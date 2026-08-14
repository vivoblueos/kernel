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

//! ESP32-C3 on-chip flash loadable-image Misc device.
//!
//! Mechanism only: erase/program/read + stateless executable mapping. The device
//! holds no image semantics (no Ready state, no image_size, no CRC, no ELF
//! knowledge). Persisted metadata + verification + recovery live in userspace.

use crate::{
    devices::{Device, DeviceClass, DeviceId, DeviceManager},
    drivers::flash::{
        flash_mmap::{self, ExecMapping, MapError},
        internal_flash::{
            with_internal_flash, with_internal_flash_exclusive, EspFlashError,
            ESP_FLASH_SECTOR_SIZE,
        },
    },
    sync::SpinLock,
};
use alloc::{string::String, sync::Arc};
use embedded_io::ErrorKind;

pub const ESP32_FLASH_DEVICE_NAME: &str = "esp32-flash0";
const ESP32_FLASH_DEVICE_MAJOR: usize = 1;
const ESP32_FLASH_DEVICE_MINOR: usize = 0x35;

// device-specific ioctl commands.
pub const ESP32_FLASH_ERASE_RANGE: u32 = 0x40;
pub const ESP32_FLASH_MAP_EXEC: u32 = 0x44;
pub const ESP32_FLASH_UNMAP: u32 = 0x45;
pub const FLASH_IOCTL_ABI_VERSION: u32 = 1;
// Returns __sys_stack_end: the safe SRAM base above kernel heap/stack, below
// which the loader may copy out-of-window RW segments. Bounds copy_rw_segments.
pub const ESP32_FLASH_QUERY_DRAM_SAFE: u32 = 0x46;
pub use crate::boards::{LOADABLE_REGION_BASE, LOADABLE_REGION_END, LOADABLE_REGION_SIZE};

#[repr(C)]
struct MapExecRequest {
    version: u32,
    size: u32,
    flags: u32,
    region_offset: u32,
    image_size: u32,
    mapped_address: u32,
}

#[repr(C)]
struct EraseRangeRequest {
    version: u32,
    size: u32,
    flags: u32,
    region_offset: u32,
    length: u32,
}

fn validate_request_header(
    version: u32,
    size: u32,
    flags: u32,
    expected_size: u32,
) -> Result<(), ErrorKind> {
    if version != FLASH_IOCTL_ABI_VERSION || size != expected_size || flags != 0 {
        return Err(ErrorKind::InvalidInput);
    }
    Ok(())
}

/// Fixed on-chip flash region; callers use relative offsets.
#[derive(Debug, Clone, Copy)]
pub struct InternalFlashRegion {
    base: u32,
    size: u32,
}

impl InternalFlashRegion {
    pub const fn new(base: u32, size: u32) -> Self {
        Self { base, size }
    }

    pub const fn size(&self) -> u32 {
        self.size
    }

    pub const fn base(&self) -> u32 {
        self.base
    }

    pub fn absolute_offset(&self, relative_offset: u32, len: usize) -> Result<u32, EspFlashError> {
        let len = u32::try_from(len).map_err(|_| EspFlashError::OutOfBounds)?;
        let relative_end = relative_offset
            .checked_add(len)
            .ok_or(EspFlashError::OutOfBounds)?;
        if relative_end > self.size {
            return Err(EspFlashError::OutOfBounds);
        }
        self.base
            .checked_add(relative_offset)
            .ok_or(EspFlashError::OutOfBounds)
    }

    /// Check alignment + fit.
    pub fn validate(&self, flash_capacity: u32) -> Result<(), EspFlashError> {
        if self.base % ESP_FLASH_SECTOR_SIZE as u32 != 0 {
            return Err(EspFlashError::UnalignedErase);
        }
        if self.size % ESP_FLASH_SECTOR_SIZE as u32 != 0 {
            return Err(EspFlashError::UnalignedErase);
        }
        let end = self
            .base
            .checked_add(self.size)
            .ok_or(EspFlashError::OutOfBounds)?;
        if end > flash_capacity {
            return Err(EspFlashError::OutOfBounds);
        }
        Ok(())
    }
}

#[derive(Debug)]
enum Esp32FlashState {
    Idle,
    Busy,
    Mapped { mapping: ExecMapping },
}

impl Default for Esp32FlashState {
    fn default() -> Self {
        Self::Idle
    }
}

/// Misc device exposing a fixed partition-like region of on-chip flash.
pub struct Esp32FlashDevice {
    name: String,
    region: InternalFlashRegion,
    state: SpinLock<Esp32FlashState>,
}

impl Esp32FlashDevice {
    pub fn new(name: &str, region: InternalFlashRegion) -> Self {
        Self {
            name: String::from(name),
            region,
            state: SpinLock::new(Esp32FlashState::Idle),
        }
    }

    fn begin_flash_operation(&self) -> Result<(), ErrorKind> {
        let mut state = self.state.irqsave_lock();
        match &*state {
            Esp32FlashState::Idle => {
                *state = Esp32FlashState::Busy;
                Ok(())
            }
            Esp32FlashState::Mapped { .. } => Err(ErrorKind::PermissionDenied),
            Esp32FlashState::Busy => Err(ErrorKind::Other),
        }
    }

    fn finish_flash_operation(&self) {
        *self.state.irqsave_lock() = Esp32FlashState::Idle;
    }

    fn ioctl_erase_range(&self, arg: usize) -> Result<(), ErrorKind> {
        if arg == 0 || arg % core::mem::align_of::<EraseRangeRequest>() != 0 {
            return Err(ErrorKind::InvalidInput);
        }

        let req = unsafe { core::ptr::read_volatile(arg as *const EraseRangeRequest) };
        validate_request_header(
            req.version,
            req.size,
            req.flags,
            core::mem::size_of::<EraseRangeRequest>() as u32,
        )?;
        if req.length == 0
            || req.region_offset % ESP_FLASH_SECTOR_SIZE as u32 != 0
            || req.length % ESP_FLASH_SECTOR_SIZE as u32 != 0
        {
            return Err(ErrorKind::InvalidInput);
        }
        let physical = self
            .region
            .absolute_offset(req.region_offset, req.length as usize)
            .map_err(map_flash_err)?;

        self.begin_flash_operation()?;
        let result = with_internal_flash(|flash| flash.erase_region(physical, req.length))
            .map_err(map_flash_err);
        self.finish_flash_operation();
        result
    }

    fn write_data(&self, pos: u64, buf: &[u8]) -> Result<usize, ErrorKind> {
        if buf.is_empty() {
            return Ok(0);
        }
        let relative = u32::try_from(pos).map_err(|_| ErrorKind::InvalidInput)?;
        let physical = self
            .region
            .absolute_offset(relative, buf.len())
            .map_err(map_flash_err)?;

        self.begin_flash_operation()?;
        let result = with_internal_flash(|flash| flash.write(physical, buf)).map_err(map_flash_err);
        self.finish_flash_operation();
        result.map(|_| buf.len())
    }

    /// Map a region-relative flash range as executable.
    fn ioctl_map_exec(&self, arg: usize) -> Result<(), ErrorKind> {
        if arg == 0 || arg % core::mem::align_of::<MapExecRequest>() != 0 {
            return Err(ErrorKind::InvalidInput);
        }

        let req = unsafe { core::ptr::read_volatile(arg as *const MapExecRequest) };
        validate_request_header(
            req.version,
            req.size,
            req.flags,
            core::mem::size_of::<MapExecRequest>() as u32,
        )?;
        let size = usize::try_from(req.image_size).map_err(|_| ErrorKind::InvalidInput)?;
        if size == 0 {
            return Err(ErrorKind::InvalidInput);
        }
        let physical = self
            .region
            .absolute_offset(req.region_offset, size)
            .map_err(map_flash_err)?;

        self.begin_flash_operation()?;
        let mapping = match with_internal_flash_exclusive(|| flash_mmap::map_exec(physical, size)) {
            Ok(Ok(mapping)) => mapping,
            Ok(Err(error)) => {
                self.finish_flash_operation();
                return Err(map_mmap_err(error));
            }
            Err(error) => {
                self.finish_flash_operation();
                return Err(map_flash_err(error));
            }
        };

        unsafe {
            let out = core::ptr::addr_of_mut!((*(arg as *mut MapExecRequest)).mapped_address);
            core::ptr::write_volatile(out, mapping.segment_address as u32);
        }
        *self.state.irqsave_lock() = Esp32FlashState::Mapped { mapping };
        Ok(())
    }

    /// Release the executable mapping. Caller must not execute in the range.
    fn ioctl_unmap(&self) -> Result<(), ErrorKind> {
        let mut state = self.state.irqsave_lock();
        let old = core::mem::replace(&mut *state, Esp32FlashState::Busy);
        let mapping = match old {
            Esp32FlashState::Mapped { mapping } => mapping,
            other => {
                *state = other;
                return Err(ErrorKind::InvalidInput);
            }
        };
        drop(state);
        let result = with_internal_flash_exclusive(|| flash_mmap::unmap_exec(&mapping));
        match result {
            Ok(Ok(())) => {
                self.finish_flash_operation();
                Ok(())
            }
            Ok(Err(error)) => {
                *self.state.irqsave_lock() = Esp32FlashState::Mapped { mapping };
                Err(map_mmap_err(error))
            }
            Err(error) => {
                *self.state.irqsave_lock() = Esp32FlashState::Mapped { mapping };
                Err(map_flash_err(error))
            }
        }
    }

    /// Write __sys_stack_end (free-SRAM base for RW segments) to the caller's
    /// *mut u32. Read-only query, independent of device state, so no state lock.
    fn ioctl_query_dram_safe(&self, arg: usize) -> Result<(), ErrorKind> {
        if arg != 0 {
            let safe = core::ptr::addr_of!(crate::boot::__sys_stack_end) as u32;
            unsafe { *(arg as *mut u32) = safe };
        }
        Ok(())
    }
}

impl Device for Esp32FlashDevice {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Misc
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(ESP32_FLASH_DEVICE_MAJOR, ESP32_FLASH_DEVICE_MINOR)
    }

    fn read(&self, pos: u64, buf: &mut [u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        if matches!(*self.state.irqsave_lock(), Esp32FlashState::Busy) {
            return Err(ErrorKind::Other);
        }
        if pos >= self.region.size() as u64 {
            return Ok(0);
        }
        let available = self.region.size() as u64 - pos;
        let count = core::cmp::min(buf.len() as u64, available) as usize;
        if count == 0 {
            return Ok(0);
        }
        let relative = u32::try_from(pos).map_err(|_| ErrorKind::InvalidInput)?;
        let physical = self
            .region
            .absolute_offset(relative, count)
            .map_err(map_flash_err)?;
        with_internal_flash(|flash| flash.read(physical, &mut buf[..count]))
            .map_err(map_flash_err)?;
        Ok(count)
    }

    fn write(&self, pos: u64, buf: &[u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        self.write_data(pos, buf)
    }

    fn ioctl(&self, request: u32, arg: usize) -> Result<(), ErrorKind> {
        match request {
            ESP32_FLASH_ERASE_RANGE => self.ioctl_erase_range(arg),
            ESP32_FLASH_MAP_EXEC => self.ioctl_map_exec(arg),
            ESP32_FLASH_UNMAP => self.ioctl_unmap(),
            ESP32_FLASH_QUERY_DRAM_SAFE => self.ioctl_query_dram_safe(arg),
            _ => Err(ErrorKind::Unsupported),
        }
    }

    fn capacity(&self) -> Result<u64, ErrorKind> {
        Ok(self.region.size() as u64)
    }

    fn sector_size(&self) -> Result<u16, ErrorKind> {
        Ok(ESP_FLASH_SECTOR_SIZE as u16)
    }

    fn sync(&self) -> Result<(), ErrorKind> {
        Ok(())
    }
}

fn map_flash_err(e: EspFlashError) -> ErrorKind {
    match e {
        EspFlashError::OutOfBounds | EspFlashError::InvalidLength => ErrorKind::InvalidInput,
        EspFlashError::ProtectedRange => ErrorKind::PermissionDenied,
        EspFlashError::UnalignedErase | EspFlashError::UnalignedWrite => ErrorKind::InvalidInput,
        EspFlashError::Busy => ErrorKind::Other,
        EspFlashError::RomError(_) | EspFlashError::VerifyFailed => ErrorKind::Other,
    }
}

fn map_mmap_err(e: MapError) -> ErrorKind {
    match e {
        MapError::AlreadyMapped => ErrorKind::PermissionDenied,
        MapError::ZeroSize
        | MapError::OutOfRange
        | MapError::Overflow
        | MapError::InvalidHandle => ErrorKind::InvalidInput,
    }
}

pub fn init_esp32_flash_device() -> Result<(), ErrorKind> {
    let region = InternalFlashRegion::new(LOADABLE_REGION_BASE, LOADABLE_REGION_SIZE);
    let capacity = with_internal_flash(|flash| Ok(flash.capacity())).map_err(map_flash_err)?;
    region.validate(capacity).map_err(map_flash_err)?;

    let device = Arc::new(Esp32FlashDevice::new(ESP32_FLASH_DEVICE_NAME, region));
    DeviceManager::get().register_device(String::from(ESP32_FLASH_DEVICE_NAME), device)?;
    log::info!(
        "esp32-flash0: region base={:#x} size={:#x}",
        LOADABLE_REGION_BASE,
        LOADABLE_REGION_SIZE
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn region() -> InternalFlashRegion {
        InternalFlashRegion::new(LOADABLE_REGION_BASE, LOADABLE_REGION_SIZE)
    }

    #[test]
    fn loadable_region_reserves_one_mib() {
        assert_eq!(LOADABLE_REGION_BASE, 0x0020_0000);
        assert_eq!(LOADABLE_REGION_SIZE, 0x0010_0000);
        assert_eq!(LOADABLE_REGION_END, 0x0030_0000);
    }

    fn map_request(region_offset: u32, image_size: u32) -> MapExecRequest {
        MapExecRequest {
            version: FLASH_IOCTL_ABI_VERSION,
            size: core::mem::size_of::<MapExecRequest>() as u32,
            flags: 0,
            region_offset,
            image_size,
            mapped_address: 0,
        }
    }

    #[test]
    fn region_absolute_offset_basic() {
        assert_eq!(region().absolute_offset(0, 0), Ok(LOADABLE_REGION_BASE));
        assert_eq!(
            region().absolute_offset(0x000F_0000, 0x1CFC),
            Ok(LOADABLE_REGION_BASE + 0x000F_0000)
        );
    }

    #[test]
    fn region_absolute_offset_rejects_overflow() {
        assert_eq!(
            region().absolute_offset(LOADABLE_REGION_SIZE, 1),
            Err(EspFlashError::OutOfBounds)
        );
        assert!(region()
            .absolute_offset(LOADABLE_REGION_SIZE - 4, 4)
            .is_ok());
        assert_eq!(
            region().absolute_offset(LOADABLE_REGION_SIZE - 4, 5),
            Err(EspFlashError::OutOfBounds)
        );
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn region_absolute_offset_rejects_usize_length_narrowing() {
        let len = usize::try_from(u64::from(u32::MAX) + 1).unwrap();
        assert_eq!(
            region().absolute_offset(0, len),
            Err(EspFlashError::OutOfBounds)
        );
    }

    #[test]
    fn region_validation_checks_alignment_and_capacity() {
        assert!(region().validate(0x0040_0000).is_ok());
        assert_eq!(
            InternalFlashRegion::new(LOADABLE_REGION_BASE + 1, LOADABLE_REGION_SIZE)
                .validate(0x0040_0000),
            Err(EspFlashError::UnalignedErase)
        );
        assert_eq!(
            InternalFlashRegion::new(LOADABLE_REGION_BASE, LOADABLE_REGION_SIZE + 1)
                .validate(0x0040_0000),
            Err(EspFlashError::UnalignedErase)
        );
        assert_eq!(
            region().validate(LOADABLE_REGION_END - 1),
            Err(EspFlashError::OutOfBounds)
        );
    }

    #[test]
    fn request_structs_use_versioned_abi_prefix() {
        assert_eq!(core::mem::size_of::<MapExecRequest>(), 24);
        assert_eq!(core::mem::offset_of!(MapExecRequest, version), 0);
        assert_eq!(core::mem::offset_of!(MapExecRequest, size), 4);
        assert_eq!(core::mem::offset_of!(MapExecRequest, flags), 8);
        assert_eq!(core::mem::offset_of!(MapExecRequest, region_offset), 12);
        assert_eq!(core::mem::offset_of!(MapExecRequest, image_size), 16);
        assert_eq!(core::mem::offset_of!(MapExecRequest, mapped_address), 20);

        assert_eq!(core::mem::size_of::<EraseRangeRequest>(), 20);
        assert_eq!(core::mem::offset_of!(EraseRangeRequest, version), 0);
        assert_eq!(core::mem::offset_of!(EraseRangeRequest, size), 4);
        assert_eq!(core::mem::offset_of!(EraseRangeRequest, flags), 8);
        assert_eq!(core::mem::offset_of!(EraseRangeRequest, region_offset), 12);
        assert_eq!(core::mem::offset_of!(EraseRangeRequest, length), 16);
    }

    #[test]
    fn request_header_checks_version_size_and_flags() {
        let expected = core::mem::size_of::<MapExecRequest>() as u32;
        assert_eq!(
            validate_request_header(FLASH_IOCTL_ABI_VERSION, expected, 0, expected),
            Ok(())
        );
        assert_eq!(
            validate_request_header(FLASH_IOCTL_ABI_VERSION + 1, expected, 0, expected),
            Err(ErrorKind::InvalidInput)
        );
        assert_eq!(
            validate_request_header(FLASH_IOCTL_ABI_VERSION, expected - 4, 0, expected),
            Err(ErrorKind::InvalidInput)
        );
        assert_eq!(
            validate_request_header(FLASH_IOCTL_ABI_VERSION, expected, 1, expected),
            Err(ErrorKind::InvalidInput)
        );
    }

    #[test]
    fn mapped_state_rejects_flash_mutation() {
        let dev = Esp32FlashDevice::new(ESP32_FLASH_DEVICE_NAME, region());
        *dev.state.irqsave_lock() = Esp32FlashState::Mapped {
            mapping: ExecMapping::for_test(),
        };
        assert_eq!(
            dev.begin_flash_operation(),
            Err(ErrorKind::PermissionDenied)
        );
    }

    #[test]
    fn map_exec_validates_request_before_hardware() {
        let dev = Esp32FlashDevice::new(ESP32_FLASH_DEVICE_NAME, region());

        let mut zero = map_request(0, 0);
        assert_eq!(
            dev.ioctl_map_exec(&mut zero as *mut MapExecRequest as usize),
            Err(ErrorKind::InvalidInput)
        );

        let mut outside = map_request(LOADABLE_REGION_SIZE, 1);
        assert_eq!(
            dev.ioctl_map_exec(&mut outside as *mut MapExecRequest as usize),
            Err(ErrorKind::InvalidInput)
        );

        let mut bad_version = map_request(0, 4);
        bad_version.version += 1;
        assert_eq!(
            dev.ioctl_map_exec(&mut bad_version as *mut MapExecRequest as usize),
            Err(ErrorKind::InvalidInput)
        );
    }

    #[test]
    fn read_at_region_end_short_circuits_without_hardware() {
        let dev = Esp32FlashDevice::new(ESP32_FLASH_DEVICE_NAME, region());
        let mut buf = [0u8; 8];
        assert_eq!(
            dev.read(LOADABLE_REGION_SIZE as u64, &mut buf, false),
            Ok(0)
        );
    }
}
