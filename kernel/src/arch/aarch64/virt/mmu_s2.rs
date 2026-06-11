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

use crate::arch::aarch64::registers::{vtcr_el2::VTCR_EL2, vttbr_el2::VTTBR_EL2};
use tock_registers::interfaces::*;

// Structure of Page Table.
#[repr(align(4096))]
#[derive(Clone, Copy)]
struct S2PageTable([u64; 512]);

const POOL_SIZE: usize = 256;
static mut PAGE_TABLE_POOL: [S2PageTable; POOL_SIZE] = [S2PageTable([0; 512]); POOL_SIZE];
static mut POOL_INDEX: usize = 0;
static mut S2_L1: S2PageTable = S2PageTable([0; 512]);

// Stage-2 Descriptor
const S2_DESC_TABLE: u64 = 3;
const S2_DESC_PAGE: u64 = 3;
const S2_ATTR_NORMAL: u64 = 0xF << 2;
const S2_ATTR_DEVICE: u64 = 1 << 2;
const S2_ATTR_S2AP_RW: u64 = 3 << 6;
const S2_ATTR_SH_INNER: u64 = 3 << 8;
const S2_ATTR_AF: u64 = 1 << 10;

fn alloc_page_table() -> Option<&'static mut S2PageTable> {
    unsafe {
        if POOL_INDEX >= POOL_SIZE {
            return None;
        }
        let table = &mut PAGE_TABLE_POOL[POOL_INDEX];
        POOL_INDEX += 1;
        for e in table.0.iter_mut() {
            *e = 0;
        }
        let start = table as *const _ as usize;
        for addr in (start..start + core::mem::size_of::<S2PageTable>()).step_by(64) {
            core::arch::asm!("dc civac, {}", in(reg) addr);
        }
        core::arch::asm!("dsb sy", options(nostack, nomem));
        Some(table)
    }
}

fn map_page(ipa: usize, pa: usize, device: bool) {
    let l1_idx = (ipa >> 30) & 0x1ff;
    let l2_idx = (ipa >> 21) & 0x1ff;
    let l3_idx = (ipa >> 12) & 0x1ff;

    unsafe {
        // L1 → L2
        let l2_table = {
            let e = S2_L1.0[l1_idx];
            if (e & 3) == S2_DESC_TABLE {
                &mut *((e & 0xFFFFFFFFF000) as *mut S2PageTable)
            } else {
                let t = alloc_page_table().expect("S2 L2 OOM");
                S2_L1.0[l1_idx] = t as *const _ as u64 | S2_DESC_TABLE;
                t
            }
        };

        // L2 → L3
        let l3_table = {
            let e = l2_table.0[l2_idx];
            if (e & 3) == S2_DESC_TABLE {
                &mut *((e & 0xFFFFFFFFF000) as *mut S2PageTable)
            } else {
                let t = alloc_page_table().expect("S2 L3 OOM");
                l2_table.0[l2_idx] = t as *const _ as u64 | S2_DESC_TABLE;
                t
            }
        };

        let attr = S2_ATTR_S2AP_RW
            | S2_ATTR_AF
            | S2_ATTR_SH_INNER
            | if device {
                S2_ATTR_DEVICE
            } else {
                S2_ATTR_NORMAL
            };
        l3_table.0[l3_idx] = (pa as u64 & 0xFFFFFFFFF000) | attr | S2_DESC_PAGE;

        let addr = &l3_table.0[l3_idx] as *const _ as usize;
        core::arch::asm!("dc civac, {}", in(reg) addr);
        core::arch::asm!("dsb sy", options(nostack, nomem));
    }
}

pub fn map_range(ipa: usize, pa: usize, size: usize, device: bool) {
    let mut offset = 0;
    while offset < size {
        map_page(ipa + offset, pa + offset, device);
        offset += 4096;
    }
}

pub fn init_stage2(ipa_base: usize, size: usize) {
    unsafe {
        POOL_INDEX = 0;
    }

    map_range(ipa_base, ipa_base, size, false);
    unsafe {
        core::arch::asm!("dsb sy", options(nostack, nomem));
        let start = &S2_L1 as *const _ as usize;
        for addr in (start..start + core::mem::size_of::<S2PageTable>()).step_by(32) {
            core::arch::asm!("dc civac, {}", in(reg) addr);
        }
        let pool_start = &PAGE_TABLE_POOL as *const _ as usize;
        let pool_end = pool_start + core::mem::size_of_val(&PAGE_TABLE_POOL);
        for addr in (pool_start..pool_end).step_by(32) {
            core::arch::asm!("dc civac, {}", in(reg) addr);
        }
        core::arch::asm!("dsb sy", options(nostack, nomem));
    }

    VTCR_EL2.write(
        VTCR_EL2::PS::PA_32B_4GB
            + VTCR_EL2::TG0::Granule4KB
            + VTCR_EL2::SH0::Inner
            + VTCR_EL2::ORGN0::NormalWBRAWA
            + VTCR_EL2::IRGN0::NormalWBRAWA
            + VTCR_EL2::SL0.val(1)
            + VTCR_EL2::T0SZ.val(32),
    );

    let vttbr = unsafe { &S2_L1 as *const _ as u64 } & !0xfff;
    VTTBR_EL2.set(vttbr);

    unsafe {
        core::arch::asm!("dsb sy", options(nostack, nomem));
        core::arch::asm!("tlbi vmalls12e1", options(nostack, nomem));
        core::arch::asm!("dsb sy", options(nostack, nomem));
        core::arch::asm!("isb sy", options(nostack, nomem));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_page_table_allocation() {
        unsafe {
            POOL_INDEX = 0;
        }

        let table1 = alloc_page_table();
        assert!(table1.is_some(), "Should allocate first table");

        unsafe {
            let idx = POOL_INDEX;
            assert_eq!(idx, 1);
        }
    }

    #[test]
    fn test_stage2_attributes_generation() {
        // Normal Memory should be 0xF << 2 (Inner & Outer WB Cacheable)
        // Device Memory should be 0x1 << 2 (Device-nGnRE)

        let attr_normal = S2_ATTR_S2AP_RW | S2_ATTR_AF | S2_ATTR_SH_INNER | S2_ATTR_NORMAL;
        let attr_device = S2_ATTR_S2AP_RW | S2_ATTR_AF | S2_ATTR_SH_INNER | S2_ATTR_DEVICE;

        // Extract MemAttr field (Bits[5:2])
        let mem_attr_normal = (attr_normal >> 2) & 0xF;
        let mem_attr_device = (attr_device >> 2) & 0xF;

        assert_eq!(
            mem_attr_normal, 0xF,
            "Normal memory attribute must be 0b1111 to prevent Alignment Faults"
        );
        assert_eq!(
            mem_attr_device, 0x1,
            "Device memory attribute must be 0b0001"
        );
    }
}
