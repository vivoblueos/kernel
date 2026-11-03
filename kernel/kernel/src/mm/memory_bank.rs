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

//! Abstraction over the memory banks available on the hardware platform.
//!
//! A memory bank is a contiguous range of physical memory described by the
//! platform (e.g. via a devicetree or firmware-provided memory map). This
//! module collects those banks so the rest of the memory management
//! subsystem can enumerate usable physical memory without knowing how a
//! particular board reports it.

use core::ptr::addr_of;

use crate::mm::{
    kernel_virt_to_phys, CachePolicy, MemFlags, MemType, PhysicalAddress, VirtualAddress,
};
use heapless::Vec;

const MAX_REGIONS: usize = 128;

pub enum MemoryBank {
    MMIO((PhysicalAddress, PhysicalAddress)),
    RAM((PhysicalAddress, PhysicalAddress)),
}

#[derive(Debug)]
pub struct MemoryRegion {
    pub base: PhysicalAddress,
    pub flags: MemFlags,
    pub memory_type: MemType,
    pub size: usize,
    pub is_reserved: bool,
    pub name: &'static str,
}

/// Describe RAM/MMIO banks and the reserved boot image without allocating from the heap.
///
/// Returned regions are sorted and disjoint. Available RAM excludes the boot
/// image, boot data and MMIO, so consumers can use each region directly.
pub fn create_memory_region_from_memory_bank(
    banks: &[MemoryBank],
) -> Vec<MemoryRegion, MAX_REGIONS> {
    let mut all_regions = Vec::new();
    let mut push = |r: MemoryRegion| {
        if r.size > 0 {
            all_regions.push(r).expect("too many memory regions");
        }
    };

    let physical = |addr: usize| kernel_virt_to_phys(VirtualAddress::new(addr));
    let kernel_start = physical(addr_of!(__text_start) as usize).into_raw();

    for bank in banks {
        let (start, end) = match bank {
            MemoryBank::RAM(range) => range,
            MemoryBank::MMIO(range) => {
                push(MemoryRegion {
                    base: range.0,
                    flags: MemFlags::READ | MemFlags::WRITE,
                    memory_type: MemType::Device,
                    size: range
                        .1
                        .into_raw()
                        .checked_sub(range.0.into_raw())
                        .expect("reversed MMIO bank"),
                    is_reserved: true,
                    name: "MMIO",
                });
                continue;
            }
        };
        assert!(start.into_raw() <= end.into_raw(), "reversed memory bank");
        if start.into_raw() < kernel_start {
            // Preserve firmware/boot data before the image (e.g. QEMU's FDT).
            push(MemoryRegion {
                base: *start,
                flags: MemFlags::READ | MemFlags::WRITE,
                memory_type: MemType::Normal(CachePolicy::WriteBack),
                size: end.into_raw().min(kernel_start) - start.into_raw(),
                is_reserved: true,
                name: "boot data",
            });
        }
    }

    // Extend sections to the next linker boundary to reserve their alignment
    // padding too. The entire image through _end must remain unavailable.
    push(MemoryRegion {
        base: physical(addr_of!(__text_start) as usize),
        flags: MemFlags::READ | MemFlags::EXECUTE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        size: addr_of!(__rodata_start) as usize - addr_of!(__text_start) as usize,
        is_reserved: true,
        name: ".text",
    });
    push(MemoryRegion {
        base: physical(addr_of!(__rodata_start) as usize),
        size: addr_of!(__data_start) as usize - addr_of!(__rodata_start) as usize,
        flags: MemFlags::READ,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        is_reserved: true,
        name: ".rodata",
    });
    push(MemoryRegion {
        base: physical(addr_of!(__data_start) as usize),
        size: addr_of!(__bss_start) as usize - addr_of!(__data_start) as usize,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        is_reserved: true,
        name: ".data .tdata .tbss .percpu",
    });
    push(MemoryRegion {
        base: physical(addr_of!(__bss_start) as usize),
        size: addr_of!(__sys_stack_start) as usize - addr_of!(__bss_start) as usize,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        is_reserved: true,
        name: ".bss .init_array .bk_app_array",
    });
    push(MemoryRegion {
        base: physical(addr_of!(__sys_stack_start) as usize),
        size: addr_of!(__sys_stack_end) as usize - addr_of!(__sys_stack_start) as usize,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        is_reserved: true,
        name: "boot stack",
    });
    push(MemoryRegion {
        base: physical(addr_of!(__sys_stack_end) as usize),
        size: addr_of!(_end) as usize - addr_of!(__sys_stack_end) as usize,
        flags: MemFlags::READ | MemFlags::WRITE,
        memory_type: MemType::Normal(CachePolicy::WriteBack),
        is_reserved: true,
        name: "boot page table",
    });

    for region in &all_regions {
        let end = region
            .base
            .into_raw()
            .checked_add(region.size)
            .expect("reserved region overflow");
        #[cfg(paging)]
        {
            let page_size =
                <crate::arch::page::PageEntry as crate::mm::paging::PageFormat>::PAGE_SIZE;
            assert!(
                (region.base.into_raw() | end) & (page_size - 1) == 0,
                "reserved region boundaries must be page aligned"
            );
        }
        if !matches!(region.memory_type, MemType::Device) {
            assert!(
                banks.iter().any(|bank| matches!(bank,
                    MemoryBank::RAM((start, ram_end))
                        if region.base.into_raw() >= start.into_raw() && end <= ram_end.into_raw()
                )),
                "reserved region lies outside every RAM bank"
            );
        }
    }
    for bank in banks {
        let MemoryBank::RAM((start, end)) = bank else {
            continue;
        };
        let ram = MemoryRegion {
            base: *start,
            flags: MemFlags::READ | MemFlags::WRITE,
            memory_type: MemType::Normal(CachePolicy::WriteBack),
            size: end.into_raw() - start.into_raw(),
            is_reserved: false,
            name: "RAM",
        };
        let holes = carve_ram_holes(&ram, all_regions.iter().filter(|r| r.is_reserved))
            .expect("invalid RAM regions");
        for (base, size) in holes {
            all_regions
                .push(MemoryRegion { base, size, ..ram })
                .expect("too many memory regions");
        }
    }
    all_regions.sort_unstable_by_key(|region| region.base.into_raw());
    assert!(
        all_regions
            .windows(2)
            .all(|pair| { pair[0].base.into_raw() + pair[0].size <= pair[1].base.into_raw() }),
        "overlapping physical memory regions"
    );
    all_regions
}

/// Split `ram` into the page-aligned sub-ranges not covered by `reserved`.
///
/// Reservations are clipped to the RAM window; every surviving boundary must
/// stay page aligned so `map_range` accepts the carved segments. The returned
/// segments are sorted and never overlap a reservation.
pub(crate) fn carve_ram_holes<'a>(
    ram: &MemoryRegion,
    reserved: impl IntoIterator<Item = &'a MemoryRegion>,
) -> Result<Vec<(PhysicalAddress, usize), 8>, &'static str> {
    #[cfg(paging)]
    let page_size = <crate::arch::page::PageEntry as crate::mm::paging::PageFormat>::PAGE_SIZE;
    let ram_start = ram.base.into_raw();
    let ram_end = ram_start
        .checked_add(ram.size)
        .ok_or("RAM region overflow")?;
    if ram.size == 0 {
        return Ok(Vec::new());
    }
    #[cfg(paging)]
    if (ram_start | ram_end) & (page_size - 1) != 0 {
        return Err("RAM region boundaries must be page aligned");
    }
    let mut spans: Vec<(usize, usize), 8> = Vec::new();
    for region in reserved {
        let start = region.base.into_raw().max(ram_start);
        let end = region
            .base
            .into_raw()
            .checked_add(region.size)
            .ok_or("reserved region overflow")?
            .min(ram_end);
        if start >= end {
            continue;
        }
        #[cfg(paging)]
        if (start | end) & (page_size - 1) != 0 {
            return Err("reservation boundaries must be page aligned");
        }
        spans
            .push((start, end))
            .map_err(|_| "too many reservations in one RAM bank")?;
    }
    spans.sort_unstable();
    let mut holes: Vec<(PhysicalAddress, usize), 8> = Vec::new();
    let mut cursor = ram_start;
    for (start, end) in spans {
        if start > cursor {
            holes
                .push((PhysicalAddress::new(cursor), start - cursor))
                .map_err(|_| "too many free segments in one RAM bank")?;
        }
        cursor = cursor.max(end);
    }
    if cursor < ram_end {
        holes
            .push((PhysicalAddress::new(cursor), ram_end - cursor))
            .map_err(|_| "too many free segments in one RAM bank")?;
    }
    Ok(holes)
}

unsafe extern "C" {
    static __text_start: u8;
    static __rodata_start: u8;
    static __data_start: u8;
    static __bss_start: u8;
    static __sys_stack_start: u8;
    static __sys_stack_end: u8;
    static _end: u8;
}
