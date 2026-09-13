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

//! ESP32-C6 mask-ROM SPI flash adapter.
//!
//! Uses the `spiflash_legacy` ROM API (esp_rom_spiflash_*), reached by documented
//! ROM addresses because this board does not link the C6 ROM script. The legacy
//! API takes no `esp_flash_t*` chip handle; the newer `esp_flash_t` API needs
//! `esp_flash_default_chip` (@0x4087FFE8) which stays NULL because BlueOS does
//! not run ESP-IDF's `esp_flash_init_default_chip()`, so all chip-based calls
//! dereferenced NULL and returned garbage (rc=24579 -> EIO -5).

use crate::arch::{disable_local_irq_save, enable_local_irq_restore};

pub const ESP_ROM_SPIFLASH_RESULT_OK: i32 = 0;
pub const ESP_ROM_SPIFLASH_RESULT_ERR: i32 = 1;
pub const ESP_ROM_SPIFLASH_RESULT_TIMEOUT: i32 = 2;

const DISABLE_CACHE: usize = 0x4000_01F0;
const RESTORE_CACHE: usize = 0x4000_01F4;
const SPIFLASH_UNLOCK: usize = 0x4000_0154;
const ESP_ROM_SPIFLASH_READ: usize = 0x4000_0150;
const ESP_ROM_SPIFLASH_WRITE: usize = 0x4000_014C;
const ESP_ROM_SPIFLASH_ERASE_SECTOR: usize = 0x4000_0144;
const ESP_ROM_SPIFLASH_ERASE_BLOCK: usize = 0x4000_0148;
const SPI_FLASH_GET_CHIP_SIZE: usize = 0x4000_01E0;
const CACHE_MSPI_MMU_SET: usize = 0x4000_06B8;
const CACHE_INVALIDATE_ICACHE_ALL: usize = 0x4000_064C;
const SPI_MEM_MMU_ITEM_CONTENT: usize = 0x6000_237C;
const SPI_MEM_MMU_ITEM_INDEX: usize = 0x6000_2380;

#[inline(always)]
unsafe fn call0(addr: usize) -> i32 {
    let f: unsafe extern "C" fn() -> i32 = core::mem::transmute(addr);
    f()
}

#[inline(always)]
unsafe fn rom_spiflash_read(src_addr: u32, data: *const u32, len: u32) -> i32 {
    let f: unsafe extern "C" fn(u32, *const u32, u32) -> i32 =
        core::mem::transmute(ESP_ROM_SPIFLASH_READ);
    f(src_addr, data, len)
}

#[inline(always)]
unsafe fn rom_spiflash_write(dest_addr: u32, data: *const u32, len: u32) -> i32 {
    let f: unsafe extern "C" fn(u32, *const u32, u32) -> i32 =
        core::mem::transmute(ESP_ROM_SPIFLASH_WRITE);
    f(dest_addr, data, len)
}

// ROM takes a sector INDEX (byte_off / 4096), not a byte offset.
#[inline(always)]
unsafe fn rom_spiflash_erase_sector(sector_number: u32) -> i32 {
    let f: unsafe extern "C" fn(u32) -> i32 = core::mem::transmute(ESP_ROM_SPIFLASH_ERASE_SECTOR);
    f(sector_number)
}

// ROM takes a 64KB block INDEX (byte_off / 65536), not a byte offset.
#[inline(always)]
unsafe fn rom_spiflash_erase_block(block_number: u32) -> i32 {
    let f: unsafe extern "C" fn(u32) -> i32 = core::mem::transmute(ESP_ROM_SPIFLASH_ERASE_BLOCK);
    f(block_number)
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) fn with_flash_op_c6<R>(body: impl FnOnce() -> R) -> R {
    let flags = disable_local_irq_save();
    let mut cache_state = 0;
    unsafe {
        let f: unsafe extern "C" fn(u32, *mut u32) = core::mem::transmute(DISABLE_CACHE);
        f(0, &mut cache_state);
    }
    let result = body();
    unsafe {
        let f: unsafe extern "C" fn(u32, u32) = core::mem::transmute(RESTORE_CACHE);
        f(0, cache_state);
    }
    enable_local_irq_restore(flags);
    result
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_read(src_addr: u32, data: *const u32, len: u32) -> i32 {
    with_flash_op_c6(|| unsafe { rom_spiflash_read(src_addr, data, len) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_write(dest_addr: u32, data: *const u32, len: u32) -> i32 {
    with_flash_op_c6(|| unsafe { rom_spiflash_write(dest_addr, data, len) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_erase_sector(sector_index: u32) -> i32 {
    with_flash_op_c6(|| unsafe { rom_spiflash_erase_sector(sector_index) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_erase_block(block_index: u32) -> i32 {
    with_flash_op_c6(|| unsafe { rom_spiflash_erase_block(block_index) })
}

pub(crate) unsafe fn rom_unlock() -> i32 {
    unsafe { call0(SPIFLASH_UNLOCK) }
}

pub(crate) unsafe fn rom_chip_size() -> u32 {
    // Legacy ROM query populated by the bootloader; safe before any chip-driver init.
    let f: unsafe extern "C" fn() -> u32 = core::mem::transmute(SPI_FLASH_GET_CHIP_SIZE);
    f()
}

pub(crate) unsafe fn rom_invalidate_icache_all() {
    let f: unsafe extern "C" fn() = core::mem::transmute(CACHE_INVALIDATE_ICACHE_ALL);
    f();
}

// C6 uses a single unified I/D cache MMU table; mappings are explicitly
// installed at the virtual address requested by the ELF linker script.
#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_map(vaddr: u32, paddr: u32, num_pages: u32) -> i32 {
    let f: unsafe extern "C" fn(u32, u32, u32, u32, u32, u32, u32) -> i32 =
        core::mem::transmute(CACHE_MSPI_MMU_SET);
    with_flash_op_c6(|| unsafe { f(0, 0, vaddr, paddr, 64, num_pages, 0) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_map_d(vaddr: u32, paddr: u32, num_pages: u32) -> i32 {
    rom_mmu_map(vaddr, paddr, num_pages)
}

pub(crate) unsafe fn rom_mmu_unmap(entry_id: u32) {
    core::ptr::write_volatile(SPI_MEM_MMU_ITEM_INDEX as *mut u32, entry_id);
    core::ptr::write_volatile(SPI_MEM_MMU_ITEM_CONTENT as *mut u32, 0);
}
