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

//! Physical page frames backing RISC-V Sv39 page tables (roadmap #1, M0).
//!
//! Lives inside `allocator` because that is the only place the buddy
//! allocator is reachable: `buddy` is a private module of `allocator`.
//!
//! Order 0 of the buddy allocator is exactly one 4 KiB page, which is also the
//! Sv39 granule, so a frame is a single order-0 allocation.

use super::{buddy, BUDDY_ALLOC};
use crate::arch::riscv::mmu::{set_frame_allocator, FrameAllocator, PAGE_SIZE};

/// Frames for Sv39 page tables, sourced from the buddy allocator.
pub struct BuddyFrameAlloc;

/// Registered once during boot; `set_frame_allocator` needs a `'static`.
static BUDDY_FRAME_ALLOC: BuddyFrameAlloc = BuddyFrameAlloc;

impl FrameAllocator for BuddyFrameAlloc {
    fn alloc_frame(&self) -> Option<usize> {
        let phys = BUDDY_ALLOC.alloc_pages_phys_addr(0)?;
        // Buddy returns whatever the previous owner left behind. A page table
        // must start zeroed: a stale entry with the V bit set would silently
        // alias whatever memory its PPN happens to name.
        //
        // Writing through a physical address is sound here because the kernel
        // runs in M-mode, which is never translated — and
        // `CONFIG_KERNEL_VIRT_OFFSET == 0` makes `phys_to_virt` the identity.
        unsafe {
            core::ptr::write_bytes(phys as *mut u8, 0, PAGE_SIZE);
        }
        Some(phys)
    }

    unsafe fn free_frame(&self, phys: usize) {
        // `pfn_to_phys(pfn) == base + (pfn << 12)`, so the pfn is recoverable
        // from the physical address. The assertion catches any future change
        // to that layout instead of freeing the wrong block.
        let pfn = BUDDY_ALLOC
            .phys_to_pfn(phys)
            .expect("frame address does not map back to its pfn");
        debug_assert_eq!(
            BUDDY_ALLOC.pfn_to_phys(pfn),
            Some(phys),
            "frame address does not map back to its pfn"
        );
        unsafe {
            BUDDY_ALLOC.free_pages_pfn(pfn, 0);
        }
    }
}

/// Hand the buddy-backed allocator to the Sv39 code.
///
/// Call once the buddy allocator is initialised — any [`crate::arch::riscv::mmu`]
/// mapping before this point fails with `MapError::NoMemory`.
pub fn init_frame_allocator() {
    set_frame_allocator(&BUDDY_FRAME_ALLOC);
}

/// Allocate one zeroed 4 KiB frame for a caller that will map it itself.
///
/// Page tables get their frames through the registered [`FrameAllocator`]
/// inside `mmu`; this is the same source exposed directly, for the *data*
/// frames that back a user image's segments and stack. Ownership stays with
/// the caller: `mmu::unmap_range` frees page-table frames but never the frames
/// they point at, so whoever allocates here must later call
/// [`free_frame_phys`].
pub fn alloc_frame_phys() -> Option<usize> {
    <BuddyFrameAlloc as FrameAllocator>::alloc_frame(&BUDDY_FRAME_ALLOC)
}

/// Release a frame returned by [`alloc_frame_phys`].
///
/// # Safety
///
/// `phys` must come from [`alloc_frame_phys`] and must no longer be reachable
/// from any live page table — freeing a mapped frame hands live memory back to
/// the allocator.
pub unsafe fn free_frame_phys(phys: usize) {
    unsafe { <BuddyFrameAlloc as FrameAllocator>::free_frame(&BUDDY_FRAME_ALLOC, phys) }
}
