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

//! ESP32-C3 Flash MMU executable mapping (XIP) for the Loadable Region.
//!
//! The 2nd-stage bootloader maps only the kernel's own IROM/DROM segments; the
//! Loadable Region is NOT pre-mapped. `map_exec` programs the
//! MMU table entry for each 64 KB page, then invalidates ICache + `fence.i`;
//! `unmap_exec` invalidates the entries.
//!
//! The C3 is ICache-only with a single shared MMU table: IROM and DROM vaddrs
//! at the same offset resolve to one entry (`(vaddr & 0x7FFFFF) >> 16`).
//! `map_exec` therefore calls both `Cache_Ibus_MMU_Set` and `Cache_Dbus_MMU_Set`
//! so the image is reachable as code (I-bus) and data (D-bus); both land on the
//! same entry, so `unmap_exec` writes it once to clear both views.

use super::esp32_rom;
use crate::{
    boards::{
        DROM_VADDR_BASE, IROM_VADDR_BASE, LOADABLE_REGION_BASE, LOADABLE_REGION_END,
        LOADABLE_REGION_SIZE,
    },
    sync::SpinLock,
};
// 64 KB. Hardware constrains vaddr%PAGE == paddr%PAGE.
pub use crate::boards::FLASH_MMU_PAGE_SIZE;

const FLASH_MMU_VADDR_MASK: u32 = 0x007F_FFFF;
const FLASH_MMU_PAGE_SHIFT: u32 = 16;
const ESP_ROM_MMU_MAP_OK: i32 = 0;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum MapError {
    ZeroSize,
    OutOfRange,
    Overflow,
    AlreadyMapped,
    InvalidHandle,
}

/// Executable mapping handle. `segment_address` is the entry the Loader jumps
/// to; the rest describe the page-aligned mapping for unmap.
#[derive(Debug)]
pub struct ExecMapping {
    pub segment_address: usize,
    pub mapped_page_address: usize,
    pub mapped_size: usize,
    pub physical_page_base: u32,
    pub page_offset: usize,
    handle: u64,
}

struct MmapState {
    live_handle: Option<u64>,
    next_handle: u64,
    busy: bool,
}

impl MmapState {
    const fn new() -> Self {
        Self {
            live_handle: None,
            next_handle: 1,
            busy: false,
        }
    }
}

static MMAP_STATE: SpinLock<MmapState> = SpinLock::new(MmapState::new());

#[inline(always)]
fn instruction_fence() {
    unsafe {
        core::arch::asm!("fence.i", options(nostack, preserves_flags));
    }
}

fn align_up(value: usize, align: usize) -> Option<usize> {
    let mask = align - 1;
    value.checked_add(mask).map(|v| v & !mask)
}

/// Check `[physical_offset, physical_end)` lies inside the Loadable Region.
fn check_loadable_range(physical_offset: u32, physical_end: u32) -> Result<(), MapError> {
    if physical_offset < LOADABLE_REGION_BASE {
        return Err(MapError::OutOfRange);
    }
    if physical_end > LOADABLE_REGION_END {
        return Err(MapError::OutOfRange);
    }
    Ok(())
}

fn physical_to_irom_vaddr(physical_offset: u32) -> Result<u32, MapError> {
    IROM_VADDR_BASE
        .checked_add(physical_offset)
        .ok_or(MapError::Overflow)
}

/// Map `[physical_offset, physical_offset+size)` as executable. `segment_address`
/// is the virtual address the caller jumps to.
pub fn map_exec(physical_offset: u32, size: usize) -> Result<ExecMapping, MapError> {
    if size == 0 {
        return Err(MapError::ZeroSize);
    }
    let size_u32 = u32::try_from(size).map_err(|_| MapError::Overflow)?;
    let physical_end = physical_offset
        .checked_add(size_u32)
        .ok_or(MapError::Overflow)?;
    check_loadable_range(physical_offset, physical_end)?;

    let page_base = physical_offset & !(FLASH_MMU_PAGE_SIZE - 1);
    let page_offset = (physical_offset - page_base) as usize;
    let required_size = page_offset.checked_add(size).ok_or(MapError::Overflow)?;
    let mapped_size =
        align_up(required_size, FLASH_MMU_PAGE_SIZE as usize).ok_or(MapError::Overflow)?;
    let mapped_page_address = physical_to_irom_vaddr(page_base)?;
    let segment_address = mapped_page_address
        .checked_add(page_offset as u32)
        .ok_or(MapError::Overflow)?;

    let handle = {
        let mut state = MMAP_STATE.irqsave_lock();
        if state.live_handle.is_some() || state.busy {
            return Err(MapError::AlreadyMapped);
        }
        let handle = state.next_handle;
        state.next_handle = state.next_handle.wrapping_add(1);
        state.live_handle = Some(handle);
        state.busy = true;
        handle
    };

    #[cfg(not(test))]
    {
        // vaddr/paddr page-aligned by construction; one ROM call covers all pages
        // (linear 1:1). rc: 0=ok, 2/3/4=align/psize/range.
        let num_pages = (mapped_size / FLASH_MMU_PAGE_SIZE as usize) as u32;
        let rc = unsafe { esp32_rom::rom_mmu_map(mapped_page_address, page_base, num_pages) };
        if rc != ESP_ROM_MMU_MAP_OK {
            let mut state = MMAP_STATE.irqsave_lock();
            state.live_handle = None;
            state.busy = false;
            return Err(MapError::OutOfRange);
        }
        // Wire up the D-bus (DROM) view too — see module doc on the shared table.
        let drom_vaddr = DROM_VADDR_BASE.wrapping_add(page_base);
        let rc_d = unsafe { esp32_rom::rom_mmu_map_d(drom_vaddr, page_base, num_pages) };
        if rc_d != ESP_ROM_MMU_MAP_OK {
            let mut v = mapped_page_address;
            for _ in 0..num_pages {
                let entry_id = (v & FLASH_MMU_VADDR_MASK) >> FLASH_MMU_PAGE_SHIFT;
                unsafe { esp32_rom::rom_mmu_unmap(entry_id) };
                v += FLASH_MMU_PAGE_SIZE;
            }
            unsafe {
                esp32_rom::rom_invalidate_icache_all();
            }
            instruction_fence();
            let mut state = MMAP_STATE.irqsave_lock();
            state.live_handle = None;
            state.busy = false;
            return Err(MapError::OutOfRange);
        }
    }

    unsafe {
        esp32_rom::rom_invalidate_icache_all();
    }
    instruction_fence();

    {
        let mut state = MMAP_STATE.irqsave_lock();
        state.busy = false;
    }
    Ok(ExecMapping {
        segment_address: segment_address as usize,
        mapped_page_address: mapped_page_address as usize,
        mapped_size,
        physical_page_base: page_base,
        page_offset,
        handle,
    })
}

pub fn unmap_exec(mapping: &ExecMapping) -> Result<(), MapError> {
    {
        let mut state = MMAP_STATE.irqsave_lock();
        if state.busy {
            return Err(MapError::InvalidHandle);
        }
        match state.live_handle {
            Some(h) if h == mapping.handle => {
                state.busy = true;
            }
            Some(_) | None => return Err(MapError::InvalidHandle),
        }
    }
    #[cfg(not(test))]
    {
        let num_pages = (mapping.mapped_size / FLASH_MMU_PAGE_SIZE as usize) as u32;
        let mut vaddr = mapping.mapped_page_address as u32;
        // One write per entry clears both I-bus and D-bus views (shared table; see module doc).
        for _ in 0..num_pages {
            let entry_id = (vaddr & FLASH_MMU_VADDR_MASK) >> FLASH_MMU_PAGE_SHIFT;
            unsafe { esp32_rom::rom_mmu_unmap(entry_id) };
            vaddr += FLASH_MMU_PAGE_SIZE;
        }
    }
    unsafe {
        esp32_rom::rom_invalidate_icache_all();
    }
    instruction_fence();
    {
        let mut state = MMAP_STATE.irqsave_lock();
        state.live_handle = None;
        state.busy = false;
    }
    Ok(())
}

#[cfg(test)]
impl ExecMapping {
    // Dummy mapping for state-machine refusal tests; does NOT touch the singleton,
    // so parallel host tests never contend on MMAP_STATE.
    pub fn for_test() -> Self {
        let off = LOADABLE_REGION_BASE;
        let page_base = off & !(FLASH_MMU_PAGE_SIZE - 1);
        ExecMapping {
            segment_address: (IROM_VADDR_BASE + off) as usize,
            mapped_page_address: (IROM_VADDR_BASE + page_base) as usize,
            mapped_size: LOADABLE_REGION_SIZE as usize,
            physical_page_base: page_base,
            page_offset: (off - page_base) as usize,
            handle: 0xFFFF_FFFF,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    fn base() -> u32 {
        LOADABLE_REGION_BASE
    }

    fn end() -> u32 {
        LOADABLE_REGION_END
    }

    #[test]
    fn align_up_basic() {
        assert_eq!(align_up(0, 0x10000), Some(0));
        assert_eq!(align_up(1, 0x10000), Some(0x10000));
        assert_eq!(align_up(0x10000, 0x10000), Some(0x10000));
        assert_eq!(align_up(0x10001, 0x10000), Some(0x20000));
        assert_eq!(align_up(usize::MAX, 0x10000), None);
    }

    #[test]
    fn check_range_accepts_base() {
        assert!(check_loadable_range(base(), base() + 1).is_ok());
    }

    #[test]
    fn check_range_accepts_full_region() {
        assert!(check_loadable_range(base(), end()).is_ok());
    }

    #[test]
    fn check_range_rejects_below_base() {
        assert_eq!(
            check_loadable_range(base() - 1, base()),
            Err(MapError::OutOfRange)
        );
    }

    #[test]
    fn check_range_rejects_past_end() {
        assert_eq!(
            check_loadable_range(end(), end() + 1),
            Err(MapError::OutOfRange)
        );
        assert_eq!(
            check_loadable_range(end() - 1, end() + 1),
            Err(MapError::OutOfRange)
        );
    }

    #[test]
    fn physical_flash_offset_maps_to_expected_irom_address() {
        assert_eq!(
            physical_to_irom_vaddr(LOADABLE_REGION_BASE),
            Ok(IROM_VADDR_BASE + LOADABLE_REGION_BASE)
        );
    }

    #[test]
    fn map_exec_rejects_zero_size() {
        clear_state();
        assert!(matches!(map_exec(base(), 0), Err(MapError::ZeroSize)));
    }

    #[test]
    fn map_exec_rejects_below_region() {
        clear_state();
        assert!(matches!(map_exec(base() - 1, 1), Err(MapError::OutOfRange)));
    }

    #[test]
    fn map_exec_rejects_past_end() {
        clear_state();
        assert!(matches!(map_exec(end(), 1), Err(MapError::OutOfRange)));
        assert!(matches!(map_exec(end() - 1, 2), Err(MapError::OutOfRange)));
    }

    #[test]
    fn map_exec_page_aligned_base_returns_identity_offset() {
        clear_state();
        let m = map_exec(base(), 4).unwrap();
        assert_eq!(m.physical_page_base, base());
        assert_eq!(m.page_offset, 0);
        assert_eq!(m.mapped_size, FLASH_MMU_PAGE_SIZE as usize);
        assert_eq!(m.segment_address, (IROM_VADDR_BASE + base()) as usize);
        assert_eq!(m.mapped_page_address, (IROM_VADDR_BASE + base()) as usize);
    }

    #[test]
    fn map_exec_intra_page_offset_preserves_page_offset() {
        clear_state();
        let off = base() + 4;
        let m = map_exec(off, 4).unwrap();
        assert_eq!(m.physical_page_base, base());
        assert_eq!(m.page_offset, 4);
        assert_eq!(m.mapped_size, FLASH_MMU_PAGE_SIZE as usize);
        assert_eq!(m.segment_address, (IROM_VADDR_BASE + off) as usize);
    }

    #[test]
    fn map_exec_spanning_two_pages_maps_two_pages() {
        clear_state();
        let off = base() + (FLASH_MMU_PAGE_SIZE - 4);
        let m = map_exec(off, 8).unwrap();
        assert_eq!(m.physical_page_base, base());
        assert_eq!(m.page_offset, (FLASH_MMU_PAGE_SIZE - 4) as usize);
        assert_eq!(m.mapped_size, 2 * FLASH_MMU_PAGE_SIZE as usize);
        assert_eq!(m.segment_address, (IROM_VADDR_BASE + off) as usize);
    }

    #[test]
    fn map_exec_size_one_byte_maps_one_page() {
        clear_state();
        let m = map_exec(base(), 1).unwrap();
        assert_eq!(m.mapped_size, FLASH_MMU_PAGE_SIZE as usize);
    }

    #[test]
    fn map_exec_size_page_minus_one_maps_one_page() {
        clear_state();
        let m = map_exec(base(), (FLASH_MMU_PAGE_SIZE - 1) as usize).unwrap();
        assert_eq!(m.mapped_size, FLASH_MMU_PAGE_SIZE as usize);
    }

    #[test]
    fn map_exec_size_exactly_page_maps_one_page() {
        clear_state();
        let m = map_exec(base(), FLASH_MMU_PAGE_SIZE as usize).unwrap();
        assert_eq!(m.mapped_size, FLASH_MMU_PAGE_SIZE as usize);
    }

    #[test]
    fn map_exec_size_page_plus_one_maps_two_pages() {
        clear_state();
        let m = map_exec(base(), (FLASH_MMU_PAGE_SIZE + 1) as usize).unwrap();
        assert_eq!(m.mapped_size, 2 * FLASH_MMU_PAGE_SIZE as usize);
    }

    #[test]
    fn map_exec_rejects_double_map() {
        clear_state();
        let _m = map_exec(base(), 4).unwrap();
        assert!(matches!(map_exec(base(), 4), Err(MapError::AlreadyMapped)));
    }

    #[test]
    fn unmap_exec_releases_then_remap_ok() {
        clear_state();
        let m = map_exec(base(), 4).unwrap();
        assert!(unmap_exec(&m).is_ok());
        assert!(map_exec(base(), 4).is_ok());
    }

    #[test]
    fn unmap_exec_rejects_double_unmap() {
        clear_state();
        let m = map_exec(base(), 4).unwrap();
        assert!(unmap_exec(&m).is_ok());
        let stale = ExecMapping {
            segment_address: 0,
            mapped_page_address: 0,
            mapped_size: 0,
            physical_page_base: 0,
            page_offset: 0,
            handle: 1,
        };
        assert_eq!(unmap_exec(&stale), Err(MapError::InvalidHandle));
    }

    #[test]
    fn unmap_exec_rejects_unknown_handle() {
        clear_state();
        let bogus = ExecMapping {
            segment_address: 0,
            mapped_page_address: 0,
            mapped_size: 0,
            physical_page_base: 0,
            page_offset: 0,
            handle: 0xDEAD,
        };
        assert_eq!(unmap_exec(&bogus), Err(MapError::InvalidHandle));
    }

    // Reset the singleton between tests.
    fn clear_state() {
        let mut s = MMAP_STATE.lock();
        s.live_handle = None;
        s.next_handle = 1;
        s.busy = false;
    }
}
