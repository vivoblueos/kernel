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

//! On-chip mask ROM spiflash + cache FFI and IRAM-resident guard wrappers.
//! Each ROM call is wrapped in the unicore flash-op guard: disable IRQ -> suspend
//! ICache -> ROM call -> resume ICache -> restore IRQ. The `.rwtext` wrappers must
//! live in IRAM: while flash is busy (erase/program) the CPU cannot fetch from flash.

use crate::{
    arch::{disable_local_irq_save, enable_local_irq_restore},
    boards::DROM_VADDR_BASE,
};

pub const ESP_ROM_SPIFLASH_RESULT_OK: i32 = 0;
pub const ESP_ROM_SPIFLASH_RESULT_ERR: i32 = 1;
pub const ESP_ROM_SPIFLASH_RESULT_TIMEOUT: i32 = 2;

// PROVIDE'd by esp32c3.rom.ld, reached via libesp_rom_sys.a -> rom-functions.x.
unsafe extern "C" {
    pub fn esp_rom_spiflash_read(src_addr: u32, data: *const u32, len: u32) -> i32;
    pub fn esp_rom_spiflash_write(dest_addr: u32, data: *const u32, len: u32) -> i32;
    pub fn esp_rom_spiflash_erase_sector(sector_number: u32) -> i32; // INDEX (byte_off / 4096)
    pub fn esp_rom_spiflash_erase_block(block_number: u32) -> i32; // 64KB INDEX
    pub fn esp_rom_spiflash_unlock() -> i32;
    fn spi_flash_get_chip_size() -> u32; // ROM-detected flash size in bytes (bootloader-filled)
    fn Cache_Suspend_ICache() -> u32; // returns autoload state
    fn Cache_Resume_ICache(state: u32);
    fn Cache_Invalidate_Addr(vaddr: u32, len: u32);
    fn Cache_Invalidate_ICache_All();
    // Returns 0 on success; 2/3/4 = vaddr-paddr unaligned / psize error / vaddr out of range.
    fn Cache_Ibus_MMU_Set(
        ext_ram: u32,
        vaddr: u32,
        paddr: u32,
        psize: u32,
        num: u32,
        fixed: u32,
    ) -> i32;
    // D-bus (DROM) counterpart; same signature/semantics as Cache_Ibus_MMU_Set.
    // C3 shares one MMU table across I-bus and D-bus (ICache-only, no DCache):
    // (vaddr & 0x7FFFFF) >> 16 yields the same entry_id for an IROM and a DROM
    // vaddr at the same offset (esp-idf hal/esp32c3 mmu_ll.h). The D-bus call
    // configures the D-bus window registers so that entry is reachable as data.
    fn Cache_Dbus_MMU_Set(
        ext_ram: u32,
        vaddr: u32,
        paddr: u32,
        psize: u32,
        num: u32,
        fixed: u32,
    ) -> i32;
}

// Flash MMU table base (EXTMEM region) and the invalid-entry sentinel (BIT(8)).
const DR_REG_MMU_TABLE: u32 = 0x600C_5000;
const SOC_MMU_INVALID: u32 = 0x100;

/// Run `body` with IRQs disabled and ICache suspended across the ROM call.
#[inline(always)]
pub(crate) fn with_flash_op<R>(body: impl FnOnce() -> R) -> R {
    let flags = disable_local_irq_save();
    let cache_state = unsafe { Cache_Suspend_ICache() };
    let result = body();
    unsafe { Cache_Resume_ICache(cache_state) };
    enable_local_irq_restore(flags);
    result
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_read(src_addr: u32, data: *const u32, len: u32) -> i32 {
    with_flash_op(|| unsafe { esp_rom_spiflash_read(src_addr, data, len) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_write(dest_addr: u32, data: *const u32, len: u32) -> i32 {
    let r = with_flash_op(|| unsafe { esp_rom_spiflash_write(dest_addr, data, len) });
    if r == ESP_ROM_SPIFLASH_RESULT_OK {
        // Drop a stale I-cache line backing the written region in case it is ever executed.
        let vaddr = DROM_VADDR_BASE.wrapping_add(dest_addr);
        unsafe { Cache_Invalidate_Addr(vaddr, len) };
    }
    r
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_erase_sector(sector_index: u32) -> i32 {
    with_flash_op(|| unsafe { esp_rom_spiflash_erase_sector(sector_index) })
}

#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_erase_block(block_index: u32) -> i32 {
    with_flash_op(|| unsafe { esp_rom_spiflash_erase_block(block_index) })
}

// IRAM-resident: suspends the unified I+D cache, so the wrapper body must be
// fetchable from IRAM (flash-backed fetches stall while suspended), same as
// rom_read/rom_write. The underlying op is a register write, not flash
// erase/program, so with_flash_op's cache guard is the only protection needed.
#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_map(vaddr: u32, paddr: u32, num_pages: u32) -> i32 {
    // fixed=0 -> linear 1:1 across `num_pages` consecutive 64KB pages.
    with_flash_op(|| unsafe { Cache_Ibus_MMU_Set(0, vaddr, paddr, 64, num_pages, 0) })
}

// D-bus (DROM) mapping, mirroring rom_mmu_map. Same .rwtext/cache-guard
// rationale: register op under the unified cache-suspend guard. `vaddr` is the
// DROM-window address (DROM_VADDR_BASE + page_base); `paddr` is unchanged
// (same physical flash page the I-bus mapping points at).
#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_map_d(vaddr: u32, paddr: u32, num_pages: u32) -> i32 {
    with_flash_op(|| unsafe { Cache_Dbus_MMU_Set(0, vaddr, paddr, 64, num_pages, 0) })
}

// Same .rwtext/cache-guard rationale as rom_mmu_map. Writes the INVALID sentinel
// (BIT(8)) to one MMU table entry, mirroring mmu_ll_set_entry_invalid.
#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_unmap(entry_id: u32) {
    with_flash_op(|| unsafe {
        *(DR_REG_MMU_TABLE as *mut u32).add(entry_id as usize) = SOC_MMU_INVALID;
    })
}

// Diagnostic: read one MMU table entry register. Pure MMIO read (no flash
// erase/program), so the cache-suspend guard is not required; runs in .rwtext
// only to keep all MMU-table access colocated.
#[link_section = ".rwtext"]
#[inline(never)]
pub(crate) unsafe fn rom_mmu_entry_read(entry_id: u32) -> u32 {
    unsafe { core::ptr::read_volatile((DR_REG_MMU_TABLE as *const u32).add(entry_id as usize)) }
}

// Called once at init with interrupts live; not cache-protected (one-shot reg clear).
pub(crate) unsafe fn rom_unlock() -> i32 {
    unsafe { esp_rom_spiflash_unlock() }
}

// ROM-detected flash capacity (filled by 1st-stage bootloader). Read-only query,
// no erase/program, so no cache guard needed.
pub(crate) unsafe fn rom_chip_size() -> u32 {
    unsafe { spi_flash_get_chip_size() }
}

// Invalidate the entire I-cache. Register op only, no erase/program.
pub(crate) unsafe fn rom_invalidate_icache_all() {
    unsafe { Cache_Invalidate_ICache_All() };
}
