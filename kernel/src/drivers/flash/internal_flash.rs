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

//! ESP32-C3 on-chip main flash raw read/write/erase driver (mask ROM spiflash API).
//! `write()` does NOT auto-erase; callers must `erase_region` first.

use super::esp32_rom;
use crate::{scheduler, sync::Mutex, time::Tick};
use core::sync::atomic::{AtomicU32, Ordering};

pub const ESP_FLASH_SECTOR_SIZE: usize = 4096;
pub const ESP_FLASH_WORD_SIZE: usize = 4;
const ROM_PAGE_SIZE: usize = 256;
const ESP_FLASH_READ_CHUNK_SIZE: usize = 1024;

/// One-shot boot unlock. Per-write re-unlock is unnecessary for the raw API.
pub(crate) fn init_internal_flash() -> Result<(), EspFlashError> {
    if !INTERNAL_FLASH_LOCK.init() {
        return Err(EspFlashError::Busy);
    }
    let r = unsafe { esp32_rom::rom_unlock() };
    if r != esp32_rom::ESP_ROM_SPIFLASH_RESULT_OK {
        log::warn!("esp_rom_spiflash_unlock returned {}", r);
        return Err(EspFlashError::RomError(r));
    }
    let chip_size = unsafe { esp32_rom::rom_chip_size() };
    INTERNAL_FLASH_CAPACITY.store(chip_size, Ordering::Release);
    log::info!(
        "internal flash ROM chip size: {} bytes ({:#x})",
        chip_size,
        chip_size
    );
    Ok(())
}

/// Serializes complete multi-call transactions after scheduling starts; boot is single-threaded.
crate::static_arc! {
    INTERNAL_FLASH_LOCK(Mutex, Mutex::new()),
}
static INTERNAL_FLASH_CAPACITY: AtomicU32 = AtomicU32::new(0);

struct InternalFlashGuard {
    locked: bool,
}

impl InternalFlashGuard {
    fn acquire() -> Result<Self, EspFlashError> {
        let locked = scheduler::is_schedule_ready();
        if locked && !INTERNAL_FLASH_LOCK.pend_for(Tick::MAX) {
            return Err(EspFlashError::Busy);
        }
        Ok(Self { locked })
    }
}

impl Drop for InternalFlashGuard {
    fn drop(&mut self) {
        if self.locked {
            INTERNAL_FLASH_LOCK.post();
        }
    }
}

pub fn with_internal_flash_exclusive<R>(operation: impl FnOnce() -> R) -> Result<R, EspFlashError> {
    let _guard = InternalFlashGuard::acquire()?;
    Ok(operation())
}

pub fn with_internal_flash<R>(
    operation: impl FnOnce(&mut Esp32c3InternalFlash) -> Result<R, EspFlashError>,
) -> Result<R, EspFlashError> {
    with_internal_flash_exclusive(|| {
        let capacity = INTERNAL_FLASH_CAPACITY.load(Ordering::Acquire);
        let mut flash = if capacity == 0 {
            Esp32c3InternalFlash::detect()?
        } else {
            Esp32c3InternalFlash::new(capacity)
        };
        operation(&mut flash)
    })?
}

/// Raw API error type.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum EspFlashError {
    OutOfBounds,
    ProtectedRange,
    InvalidLength,
    UnalignedErase,
    UnalignedWrite,
    Busy,
    RomError(i32), // ROM spiflash non-OK result (1=ERR, 2=TIMEOUT)
    VerifyFailed,
}

fn rom_result(r: i32) -> Result<(), EspFlashError> {
    if r == esp32_rom::ESP_ROM_SPIFLASH_RESULT_OK {
        Ok(())
    } else {
        Err(EspFlashError::RomError(r))
    }
}

pub struct Esp32c3InternalFlash {
    capacity: u32,
}

impl Esp32c3InternalFlash {
    pub const fn new(capacity: u32) -> Self {
        Self { capacity }
    }

    pub fn detect() -> Result<Self, EspFlashError> {
        let size = unsafe { esp32_rom::rom_chip_size() };
        Ok(Self::new(size))
    }

    pub const fn capacity(&self) -> u32 {
        self.capacity
    }

    /// `offset + len` must fit within `capacity`.
    fn check_bounds(&self, offset: u32, len: usize) -> Result<(), EspFlashError> {
        let len = u32::try_from(len).map_err(|_| EspFlashError::OutOfBounds)?;
        let end = offset.checked_add(len).ok_or(EspFlashError::OutOfBounds)?;
        if end > self.capacity {
            return Err(EspFlashError::OutOfBounds);
        }
        Ok(())
    }

    /// Read `buf.len()` bytes from `offset`. ROM takes a 4-aligned `*const u32`,
    /// so unaligned head/tail are staged through a word buffer.
    pub fn read(&mut self, offset: u32, buf: &mut [u8]) -> Result<(), EspFlashError> {
        self.check_bounds(offset, buf.len())?;
        if buf.is_empty() {
            return Ok(());
        }

        let mut done = 0usize;
        let head_mis = (offset as usize) & (ESP_FLASH_WORD_SIZE - 1);
        if head_mis != 0 {
            let word_off = offset & !(ESP_FLASH_WORD_SIZE as u32 - 1);
            let head_len = core::cmp::min(ESP_FLASH_WORD_SIZE - head_mis, buf.len());
            let mut scratch: EspAlignedBuffer<ESP_FLASH_WORD_SIZE> = EspAlignedBuffer::new();
            let r = unsafe {
                esp32_rom::rom_read(
                    word_off,
                    scratch.0.as_ptr() as *const u32,
                    ESP_FLASH_WORD_SIZE as u32,
                )
            };
            rom_result(r)?;
            buf[..head_len].copy_from_slice(&scratch.0[head_mis..head_mis + head_len]);
            done = head_len;
        }

        // Middle: 1 KiB chunks, 4-aligned length.
        let mut chunk: EspAlignedBuffer<ESP_FLASH_READ_CHUNK_SIZE> = EspAlignedBuffer::new();
        while done < buf.len() {
            let remaining = buf.len() - done;
            if remaining < ESP_FLASH_WORD_SIZE {
                break; // <4B tail handled below
            }
            let n = core::cmp::min(
                ESP_FLASH_READ_CHUNK_SIZE,
                remaining & !(ESP_FLASH_WORD_SIZE - 1),
            );
            let r = unsafe {
                esp32_rom::rom_read(
                    offset + done as u32,
                    chunk.0.as_ptr() as *const u32,
                    n as u32,
                )
            };
            rom_result(r)?;
            buf[done..done + n].copy_from_slice(&chunk.0[..n]);
            done += n;
        }

        // Tail (< 4 bytes): read one aligned word, copy the needed bytes.
        if done < buf.len() {
            let tail_off = offset + done as u32;
            let word_off = tail_off & !(ESP_FLASH_WORD_SIZE as u32 - 1);
            let skip = (tail_off - word_off) as usize;
            let tail = buf.len() - done;
            let mut scratch: EspAlignedBuffer<ESP_FLASH_WORD_SIZE> = EspAlignedBuffer::new();
            let r = unsafe {
                esp32_rom::rom_read(
                    word_off,
                    scratch.0.as_ptr() as *const u32,
                    ESP_FLASH_WORD_SIZE as u32,
                )
            };
            rom_result(r)?;
            buf[done..].copy_from_slice(&scratch.0[skip..skip + tail]);
        }
        Ok(())
    }

    /// Erase `len` bytes from `offset`; both must be 4 KB-aligned.
    pub fn erase_region(&mut self, offset: u32, len: u32) -> Result<(), EspFlashError> {
        if offset % ESP_FLASH_SECTOR_SIZE as u32 != 0 {
            return Err(EspFlashError::UnalignedErase);
        }
        if len % ESP_FLASH_SECTOR_SIZE as u32 != 0 {
            return Err(EspFlashError::UnalignedErase);
        }
        self.check_bounds(offset, len as usize)?;
        let first_sector = offset / ESP_FLASH_SECTOR_SIZE as u32;
        let sector_count = len / ESP_FLASH_SECTOR_SIZE as u32;
        for index in 0..sector_count {
            self.erase_sector(first_sector + index)?;
        }
        Ok(())
    }

    fn erase_sector(&mut self, sector: u32) -> Result<(), EspFlashError> {
        // ROM takes a sector INDEX (byte_off / 4096), not a byte offset.
        let r = unsafe { esp32_rom::rom_erase_sector(sector) };
        rom_result(r)
    }

    pub fn program_aligned(&mut self, offset: u32, data: &[u8]) -> Result<(), EspFlashError> {
        if offset % ESP_FLASH_WORD_SIZE as u32 != 0 {
            return Err(EspFlashError::UnalignedWrite);
        }
        if data.len() % ESP_FLASH_WORD_SIZE != 0 {
            return Err(EspFlashError::UnalignedWrite);
        }
        self.check_bounds(offset, data.len())?;
        if data.is_empty() {
            return Ok(());
        }
        let mut page: EspAlignedBuffer<ROM_PAGE_SIZE> = EspAlignedBuffer::new();
        let mut done = 0usize;
        while done < data.len() {
            let current_offset = offset + done as u32;
            let offset_in_page = (current_offset as usize) % ROM_PAGE_SIZE;
            let page_remaining = ROM_PAGE_SIZE - offset_in_page;
            let write_len = core::cmp::min(page_remaining, data.len() - done);
            page.0[..write_len].copy_from_slice(&data[done..done + write_len]);
            let r = unsafe {
                esp32_rom::rom_write(
                    current_offset,
                    page.0.as_ptr() as *const u32,
                    write_len as u32,
                )
            };
            rom_result(r)?;
            done += write_len;
        }
        Ok(())
    }

    /// Program arbitrary bytes without erasing. ROM calls stay 4-byte aligned,
    /// never cross a 256-byte page, and pad unaligned head/tail with 0xFF so
    /// out-of-range bytes are unchanged (NOR only clears bits).
    pub fn write(&mut self, offset: u32, data: &[u8]) -> Result<(), EspFlashError> {
        self.check_bounds(offset, data.len())?;
        if data.is_empty() {
            return Ok(());
        }

        let data_len = u32::try_from(data.len()).map_err(|_| EspFlashError::OutOfBounds)?;
        let data_end = offset
            .checked_add(data_len)
            .ok_or(EspFlashError::OutOfBounds)?;
        let mut current = offset & !(ESP_FLASH_WORD_SIZE as u32 - 1);
        let aligned_end = data_end
            .checked_add(ESP_FLASH_WORD_SIZE as u32 - 1)
            .map(|end| end & !(ESP_FLASH_WORD_SIZE as u32 - 1))
            .ok_or(EspFlashError::OutOfBounds)?;
        let mut page: EspAlignedBuffer<ROM_PAGE_SIZE> = EspAlignedBuffer::new_ff();

        while current < aligned_end {
            let page_remaining = ROM_PAGE_SIZE - current as usize % ROM_PAGE_SIZE;
            let remaining = (aligned_end - current) as usize;
            let write_len = core::cmp::min(page_remaining, remaining);
            page.0[..write_len].fill(0xFF);

            let copy_start = core::cmp::max(current, offset);
            let copy_end = core::cmp::min(current + write_len as u32, data_end);
            if copy_start < copy_end {
                let src = (copy_start - offset) as usize;
                let dst = (copy_start - current) as usize;
                let len = (copy_end - copy_start) as usize;
                page.0[dst..dst + len].copy_from_slice(&data[src..src + len]);
            }

            let r = unsafe {
                esp32_rom::rom_write(current, page.0.as_ptr() as *const u32, write_len as u32)
            };
            rom_result(r)?;
            current += write_len as u32;
        }
        Ok(())
    }
}

/// 4-byte-aligned scratch buffer, generic on `N` for word/page reuse.
#[repr(align(4))]
struct EspAlignedBuffer<const N: usize>([u8; N]);

impl<const N: usize> EspAlignedBuffer<N> {
    const fn new() -> Self {
        Self([0u8; N])
    }

    const fn new_ff() -> Self {
        Self([0xFFu8; N])
    }
}

#[cfg(test)]
mod tests {
    use super::{super::esp32_rom, *};
    use blueos_test_macro::test;

    #[test]
    fn new_sets_capacity() {
        let f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(f.capacity(), 0x0040_0000);
    }

    #[test]
    fn check_bounds_accepts_in_range() {
        let f = Esp32c3InternalFlash::new(4096);
        assert!(f.check_bounds(0, 4096).is_ok());
        assert!(f.check_bounds(0, 0).is_ok());
        assert!(f.check_bounds(4096, 0).is_ok());
    }

    #[test]
    fn check_bounds_rejects_overflow() {
        let f = Esp32c3InternalFlash::new(4096);
        assert_eq!(f.check_bounds(0, 4097), Err(EspFlashError::OutOfBounds));
        assert_eq!(f.check_bounds(1, 4096), Err(EspFlashError::OutOfBounds));
        assert_eq!(f.check_bounds(u32::MAX, 1), Err(EspFlashError::OutOfBounds));
    }

    #[test]
    fn erase_region_requires_sector_alignment() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(f.erase_region(1, 4096), Err(EspFlashError::UnalignedErase));
        assert_eq!(f.erase_region(0, 1), Err(EspFlashError::UnalignedErase));
        assert_eq!(f.erase_region(1, 0), Err(EspFlashError::UnalignedErase));
    }

    #[test]
    fn erase_region_rejects_out_of_bounds() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(
            f.erase_region(0x0040_0000, 4096),
            Err(EspFlashError::OutOfBounds)
        );
    }

    #[test]
    fn rom_result_maps_codes() {
        assert_eq!(rom_result(esp32_rom::ESP_ROM_SPIFLASH_RESULT_OK), Ok(()));
        assert_eq!(
            rom_result(esp32_rom::ESP_ROM_SPIFLASH_RESULT_ERR),
            Err(EspFlashError::RomError(1))
        );
        assert_eq!(
            rom_result(esp32_rom::ESP_ROM_SPIFLASH_RESULT_TIMEOUT),
            Err(EspFlashError::RomError(2))
        );
    }

    #[test]
    fn aligned_buffer_is_word_aligned() {
        let buf: EspAlignedBuffer<128> = EspAlignedBuffer::new();
        let addr = buf.0.as_ptr() as usize;
        assert_eq!(addr % ESP_FLASH_WORD_SIZE, 0);
    }

    #[test]
    fn program_aligned_rejects_unaligned_offset() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        let data = [0u8; 8];
        assert_eq!(
            f.program_aligned(1, &data),
            Err(EspFlashError::UnalignedWrite)
        );
        assert_eq!(
            f.program_aligned(2, &data),
            Err(EspFlashError::UnalignedWrite)
        );
        assert_eq!(
            f.program_aligned(3, &data),
            Err(EspFlashError::UnalignedWrite)
        );
    }

    #[test]
    fn program_aligned_rejects_unaligned_len() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(
            f.program_aligned(0, &[0u8; 3]),
            Err(EspFlashError::UnalignedWrite)
        );
        assert_eq!(
            f.program_aligned(0, &[0u8; 5]),
            Err(EspFlashError::UnalignedWrite)
        );
        assert_eq!(
            f.program_aligned(0, &[0u8; 7]),
            Err(EspFlashError::UnalignedWrite)
        );
    }

    #[test]
    fn program_aligned_rejects_out_of_bounds() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(
            f.program_aligned(0x0040_0000, &[0u8; 8]),
            Err(EspFlashError::OutOfBounds)
        );
    }

    #[test]
    fn program_aligned_accepts_aligned_empty() {
        let mut f = Esp32c3InternalFlash::new(0x0040_0000);
        assert_eq!(f.program_aligned(0, &[]), Ok(()));
        assert_eq!(f.program_aligned(4, &[]), Ok(()));
    }
}
