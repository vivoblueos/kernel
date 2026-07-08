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

//! ELF loader for user-space processes (AArch64).
//!
//! This module provides:
//!
//! * [`PageTableAllocator`] — an implementation of
//!   [`MemoryAllocator`] that allocates physical pages and
//!   maps them into the process's address space via the MMU.
//!
//! * [`MemoryAllocator`] — a local trait (avoids a GN dependency cycle
//!   with `blueos_loader` → `librs` → `scal` → `blueos`).
//!
//! # Constraints (Phase 3)
//!
//! * Only **ET_DYN** (PIE) ELFs are supported.
//! * The user stack is 8 KB, located at `USER_STACK_BASE`.
//! * INTERP is detected but only produces a warning — no dynamic linker
//!   loading yet.

use crate::{
    arch::aarch64::mmu::{self, map_user_range_in_pgtbl, MemAttributes, PageTableManager},
    mm::kernel_virt_to_phys,
    process::AddressSpace,
};
use core::{alloc::Layout, ptr::NonNull};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// User stack size (8 KB).
const USER_STACK_SIZE: usize = 8 * 1024;

/// Base virtual address for the user stack.
const USER_STACK_BASE: usize = 0x0000_0000_8000_0000;

/// Minimum alignment for user mappings (4 KB page).
const PAGE_ALIGN: usize = 4096;

// ---------------------------------------------------------------------------
// PageTableAllocator
// ---------------------------------------------------------------------------

/// A local `MemoryAllocator` trait mirroring the subset of
/// `blueos_loader::MemoryAllocator` needed by the kernel-side
/// [`PageTableAllocator`].
///
/// This exists only to avoid a GN dependency cycle:
/// `blueos` → `blueos_loader` → `librs` → `scal` → `blueos`.
pub(crate) trait MemoryAllocator {
    fn entry(&self) -> usize;
    fn set_entry(&mut self, entry: usize) -> &mut Self;
    fn update_start(&mut self, val: usize) -> &mut Self;
    fn update_end(&mut self, val: usize) -> &mut Self;
    fn total_size(&self) -> Result<usize>;
    fn allocate(&mut self) -> Result<()>;
    fn write_slice_at(&mut self, vaddr: usize, data: &[u8]) -> Result<usize>;
    fn write_value_at<T: Sized>(&mut self, vaddr: usize, val: T) -> Result<usize>;
    fn real_entry(&self) -> Result<usize>;
    fn real_start(&self) -> Result<usize>;
}

/// Result alias for allocator operations.
pub(crate) type Result<T> = core::result::Result<T, &'static str>;

/// A [`MemoryAllocator`] that backs ELF segments with physical pages and
/// maps them into the process's address space.
/// maps them into the process's address space.
///
/// # Lifecycle
///
/// 1. `build_memory_layout` is called externally (tracks VA range).
/// 2. `allocate()` allocates physical pages for the range and maps them
///    into `address_space`.
/// 3. `write_slice_at` / `write_value_at` copy data into the kernel-virtual
///    alias of those pages.
/// 4. `real_entry()` resolves the entry point virtual address.
pub(crate) struct PageTableAllocator {
    /// The address space to map into.
    address_space: *mut AddressSpace,

    /// Virtual entry point (set by `build_memory_layout`).
    virtual_entry: usize,

    /// Span of tracked loadable segments.
    virtual_start: usize,
    virtual_end: usize,

    /// Kernel-virtual base of the allocated page range.
    kernel_base: Option<NonNull<u8>>,

    /// Total number of bytes allocated (rounded up to page boundary).
    allocated_size: usize,
}

impl PageTableAllocator {
    /// Create a new allocator for the given address space.
    pub(crate) fn new(address_space: &AddressSpace) -> Self {
        Self {
            address_space: address_space as *const AddressSpace as *mut AddressSpace,
            virtual_entry: 0,
            virtual_start: usize::MAX,
            virtual_end: 0,
            kernel_base: None,
            allocated_size: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// MemoryAllocator trait impl
// ---------------------------------------------------------------------------

impl MemoryAllocator for PageTableAllocator {
    fn entry(&self) -> usize {
        self.virtual_entry
    }

    fn set_entry(&mut self, entry: usize) -> &mut Self {
        self.virtual_entry = entry;
        self
    }

    fn update_start(&mut self, val: usize) -> &mut Self {
        self.virtual_start = core::cmp::min(self.virtual_start, val);
        self
    }

    fn update_end(&mut self, val: usize) -> &mut Self {
        self.virtual_end = core::cmp::max(self.virtual_end, val);
        self
    }

    fn total_size(&self) -> Result<usize> {
        if self.virtual_end < self.virtual_start {
            return Err("Illegal memory size");
        }
        Ok(self.virtual_end - self.virtual_start)
    }

    fn allocate(&mut self) -> Result<()> {
        let size = self.total_size()?;
        if size == 0 {
            return Err("No memory to allocate");
        }

        // Round up to page boundary.
        let page_size =
            size.checked_add(PAGE_ALIGN - 1).ok_or("size overflow")? & !(PAGE_ALIGN - 1);

        // Allocate page-aligned kernel heap memory.
        let layout = Layout::from_size_align(page_size, PAGE_ALIGN)
            .map_err(|_| "Invalid layout for page allocation")?;
        let ptr = unsafe { alloc::alloc::alloc(layout) };
        if ptr.is_null() {
            return Err("Failed to allocate pages for ELF segment");
        }
        // Zero the memory (BSS segments require zero-initialised memory).
        unsafe {
            core::ptr::write_bytes(ptr, 0, page_size);
        }

        let kernel_va = ptr as usize;
        let phys_base = kernel_virt_to_phys(kernel_va);

        // Map into the user address space.
        let pgtbl = unsafe { &mut *(*self.address_space).root_ptr() };
        map_user_range_in_pgtbl(
            pgtbl,
            self.virtual_start,
            phys_base,
            page_size,
            MemAttributes::Normal,
        )?;

        self.kernel_base = Some(unsafe { NonNull::new_unchecked(ptr) });
        self.allocated_size = page_size;
        // Register this allocation with the address space so it is freed on drop.
        unsafe { (*self.address_space).track_alloc(ptr, layout) };
        Ok(())
    }

    fn write_slice_at(&mut self, vaddr: usize, data: &[u8]) -> Result<usize> {
        let size = data.len();
        if size == 0 {
            return Ok(size);
        }
        let dst = self.inner_real_ptr(vaddr)?;
        unsafe {
            core::ptr::copy_nonoverlapping(data.as_ptr(), dst, size);
        }
        Ok(size)
    }

    fn write_value_at<T: Sized>(&mut self, vaddr: usize, val: T) -> Result<usize> {
        let size = core::mem::size_of::<T>();
        // Bounds-check the full write range, not just the start address.
        let end = vaddr.checked_add(size).ok_or("vaddr + size overflow")?;
        if end > self.virtual_end {
            return Err("write_value_at: write would exceed allocated segment range");
        }
        let dst = self.inner_real_ptr(vaddr)? as *mut T;
        unsafe {
            dst.write(val);
        }
        Ok(size)
    }

    fn real_entry(&self) -> Result<usize> {
        Ok(self.virtual_entry)
    }

    fn real_start(&self) -> Result<usize> {
        // Return the user-space virtual load base, not the kernel VA.
        // R_AARCH64_RELATIVE relocations are patched with (virtual_start + addend).
        Ok(self.virtual_start)
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

impl PageTableAllocator {
    /// Compute the kernel-virtual address for a given user-space vaddr.
    fn inner_real_ptr(&self, vaddr: usize) -> Result<*mut u8> {
        if vaddr < self.virtual_start || vaddr >= self.virtual_end {
            return Err("The virtual address is in an illegal memory region");
        }
        let offset = vaddr - self.virtual_start;
        if offset >= self.allocated_size {
            return Err("The offset is beyond the allocated memory region");
        }
        let base = self.kernel_base.ok_or("Memory not allocated yet")?;
        Ok(unsafe { base.as_ptr().add(offset) })
    }
}

// ---------------------------------------------------------------------------
// User stack
// ---------------------------------------------------------------------------

/// Allocate an 8 KB user stack and return its top (stack pointer).
///
/// The stack is mapped at `USER_STACK_BASE` with EL0 RW permissions.
/// Returns the *top* of the stack (base + size), suitable for use as
/// the initial SP in `Context::init_el0`.
pub(crate) fn allocate_user_stack(address_space: &mut AddressSpace) -> Result<usize> {
    let pgtbl = unsafe { &mut *address_space.root_ptr() };

    // Allocate page-aligned kernel heap memory for the stack.
    let layout =
        Layout::from_size_align(USER_STACK_SIZE, PAGE_ALIGN).map_err(|_| "Invalid stack layout")?;
    let ptr = unsafe { alloc::alloc::alloc(layout) };
    if ptr.is_null() {
        return Err("Failed to allocate user stack");
    }
    // Zero the stack.
    unsafe {
        core::ptr::write_bytes(ptr, 0, USER_STACK_SIZE);
    }

    let kernel_va = ptr as usize;
    let phys_base = kernel_virt_to_phys(kernel_va);

    map_user_range_in_pgtbl(
        pgtbl,
        USER_STACK_BASE,
        phys_base,
        USER_STACK_SIZE,
        MemAttributes::Normal,
    )?;
    // Register the stack allocation so it is freed when the address space drops.
    address_space.track_alloc(ptr, layout);

    // Return the stack pointer (top of the stack).
    Ok(USER_STACK_BASE + USER_STACK_SIZE)
}
