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

//! Memory allocation abstraction for ELF loading.
//!
//! The [`MemoryAllocator`] trait decouples the ELF loader from the
//! underlying storage mechanism.  Two implementations exist:
//!
//! * [`DirectAllocator`] — heap-backed (used by the existing loader tests
//!   and the `MemoryMapper` path).
//! * `PageTableAllocator` — kernel-side, in `kernel/kernel/src/process/elf.rs`,
//!   which allocates physical pages and maps them into a user address space.

use core::alloc::Layout;

/// Error type for allocator operations.
pub type Result<T> = core::result::Result<T, &'static str>;

/// A memory allocator suitable for ELF loading.
///
/// The ELF loader needs to:
///
/// 1. Track the span of loadable segments (`update_start`, `update_end`,
///    `set_entry`, `entry`, `total_size`).
/// 2. Allocate a contiguous region large enough to hold all segments
///    (`allocate`).
/// 3. Write segment data and relocation values into that region
///    (`write_slice_at`, `write_value_at`).
/// 4. Resolve the real (runtime) address of the entry point (`real_entry`).
///
/// # Typical lifecycle
///
/// ```ignore
/// let mut alloc: impl MemoryAllocator = ...;
/// build_memory_layout(&elf, &mut alloc);   // calls update_start/end/set_entry
/// alloc.allocate()?;                        // allocate backing store
/// copy_content_to_memory(&buf, &elf, &mut alloc); // calls write_slice_at
/// relocate(&elf, &mut alloc);               // calls write_value_at
/// let entry = alloc.real_entry()?;          // resolve entry point
/// ```
pub trait MemoryAllocator {
    /// Return the currently configured entry-point virtual address.
    fn entry(&self) -> usize;

    /// Override the entry-point virtual address.
    fn set_entry(&mut self, entry: usize) -> &mut Self;

    /// Expand the tracked virtual range to include `val` at the start.
    fn update_start(&mut self, val: usize) -> &mut Self;

    /// Expand the tracked virtual range to include `val` at the end.
    fn update_end(&mut self, val: usize) -> &mut Self;

    /// Total size of the tracked virtual range (`end - start`).
    fn total_size(&self) -> Result<usize>;

    /// Allocate backing storage for the tracked virtual range.
    ///
    /// Must be called after `update_start`/`update_end` have been called
    /// for all loadable segments.
    fn allocate(&mut self) -> Result<()>;

    /// Write a byte slice at the given virtual address.
    fn write_slice_at(&mut self, vaddr: usize, data: &[u8]) -> Result<usize>;

    /// Write a value of type `T` at the given virtual address.
    fn write_value_at<T: Sized>(&mut self, vaddr: usize, val: T) -> Result<usize>;

    /// Resolve the runtime address of the entry point.
    fn real_entry(&self) -> Result<usize>;

    /// Return the base address of the allocated backing store (if known).
    fn real_start(&self) -> Result<usize>;
}

// ---------------------------------------------------------------------------
// DirectAllocator — heap-based, wraps the existing MemoryMapper logic
// ---------------------------------------------------------------------------

/// A heap-backed [`MemoryAllocator`] that mirrors the behaviour of the
/// original `MemoryMapper`.
///
/// This is the implementation used by the existing loader tests and by
/// any platform that does not use an MMU (or loads ELFs into a flat
/// address space).
#[derive(Debug)]
pub struct DirectAllocator {
    virtual_entry: usize,
    virtual_start: usize,
    virtual_end: usize,
    mem: blueos_infra::storage::Storage,
}

impl DirectAllocator {
    /// Create a new, empty allocator.
    #[inline]
    pub fn new() -> Self {
        Self {
            virtual_entry: 0,
            virtual_start: usize::MAX,
            virtual_end: 0,
            mem: blueos_infra::storage::Storage::default(),
        }
    }
}

impl Default for DirectAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryAllocator for DirectAllocator {
    #[inline]
    fn entry(&self) -> usize {
        self.virtual_entry
    }

    #[inline]
    fn set_entry(&mut self, entry: usize) -> &mut Self {
        self.virtual_entry = entry;
        self
    }

    #[inline]
    fn update_start(&mut self, val: usize) -> &mut Self {
        self.virtual_start = core::cmp::min(self.virtual_start, val);
        self
    }

    #[inline]
    fn update_end(&mut self, val: usize) -> &mut Self {
        self.virtual_end = core::cmp::max(self.virtual_end, val);
        self
    }

    #[inline]
    fn total_size(&self) -> Result<usize> {
        if self.virtual_end < self.virtual_start {
            return Err("Illegal memory size");
        }
        Ok(self.virtual_end - self.virtual_start)
    }

    fn allocate(&mut self) -> Result<()> {
        // FIXME: We are not using paging yet, so alignment (usually 4096)
        // specified in the program header is not applied here.
        // BlueKernel on AArch64 uses MMU by default, which requires aligning to
        // a page boundary.
        #[cfg(any(target_arch = "aarch64"))]
        const ALIGN: usize = 4096;
        #[cfg(not(any(target_arch = "aarch64")))]
        const ALIGN: usize = 2 * core::mem::size_of::<usize>();

        let Ok(layout) = Layout::from_size_align(self.total_size()?, ALIGN) else {
            return Err("Illegal memory layout");
        };
        self.mem = blueos_infra::storage::Storage::from_layout(layout);
        Ok(())
    }

    #[inline]
    fn write_slice_at(&mut self, vaddr: usize, data: &[u8]) -> Result<usize> {
        let size = data.len();
        if size == 0 {
            return Ok(size);
        }
        let real_begin = self.inner_real_begin(vaddr, size)?;
        // FIXME: Is it safe enough to use copy_nonoverlapping?
        unsafe { core::ptr::copy(data.as_ptr(), real_begin, data.len()) };
        Ok(size)
    }

    #[inline]
    fn write_value_at<T: Sized>(&mut self, vaddr: usize, val: T) -> Result<usize> {
        let size = core::mem::size_of::<T>();
        let real_begin = self.inner_real_begin(vaddr, size)?;
        let val_ptr: *mut T = unsafe { core::mem::transmute(real_begin) };
        unsafe { val_ptr.write(val) };
        Ok(size)
    }

    #[inline]
    fn real_entry(&self) -> Result<usize> {
        Ok(self.inner_real_ptr(self.virtual_entry)? as usize)
    }

    #[inline]
    fn real_start(&self) -> Result<usize> {
        let base = self.mem.base();
        if base.is_null() {
            return Err("Memory not allocated yet");
        }
        Ok(base as usize)
    }
}

// ---------------------------------------------------------------------------
// Internal helpers (ported from MemoryMapper)
// ---------------------------------------------------------------------------

impl DirectAllocator {
    fn inner_real_offset(&self, vaddr: usize) -> Result<usize> {
        if vaddr < self.virtual_start || vaddr >= self.virtual_end {
            return Err("The virtual address is in an illegal memory region");
        }
        let total_size = self.total_size()?;
        let offset = vaddr - self.virtual_start;
        if offset >= total_size {
            return Err("The offset is beyond the virtual memory region");
        }
        Ok(offset)
    }

    fn inner_real_ptr(&self, vaddr: usize) -> Result<*mut u8> {
        let offset = self.inner_real_offset(vaddr)?;
        if offset >= self.mem.size() {
            return Err("The offset is beyond the allocated memory region");
        }
        let base = self.mem.base();
        if base.is_null() {
            return Err("Memory not allocated yet");
        }
        Ok(unsafe { base.add(offset) })
    }

    fn inner_real_begin(&mut self, vaddr: usize, size: usize) -> Result<*mut u8> {
        if vaddr < self.virtual_start || vaddr + size > self.virtual_end {
            return Err("The span of the data is in an illegal memory region");
        }
        let real_begin = self.inner_real_ptr(vaddr)?;
        let _real_end = core::hint::black_box(self.inner_real_ptr(vaddr + size - 1)?);
        Ok(real_begin)
    }
}