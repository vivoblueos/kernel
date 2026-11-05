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

//! Flat image allocations and their authorized fixed-address regions.

use blueos_infra::storage::Storage;
use core::{
    alloc::Layout,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::{
    error::{ErrorContext, LoadErrorKind},
    memory::{
        AllocationOffset, ImageLayout, ImageMapping, ImageMemory, MemoryPermissions, Placement,
        TargetAddress,
    },
    LoadError, LoadResult,
};

/// A fixed address range authorized for the flat memory backend.
///
/// The shared occupancy flag prevents overlapping allocations from reusing the
/// same region, including allocations prepared by different mapper instances.
#[derive(Debug)]
pub struct MemoryRegion {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) permissions: MemoryPermissions,
    occupied: AtomicBool,
}

impl MemoryRegion {
    /// Authorizes a fixed address range for accesses described by `permissions`.
    ///
    /// # Safety
    ///
    /// `[start, end)` must remain valid and mapped for the advertised permissions
    /// for every mapper and allocation using it. The caller must prevent aliasing
    /// Rust references, execution, and conflicting accesses while it is borrowed.
    /// Overlapping region declarations and legacy mappers must not bypass that
    /// exclusivity; only allocations using this same declaration share its flag.
    pub const unsafe fn new(start: usize, end: usize, permissions: MemoryPermissions) -> Self {
        Self {
            start,
            end,
            permissions,
            occupied: AtomicBool::new(false),
        }
    }
}

/// Prepares heap-backed images or borrows an authorized fixed region.
///
/// Backing belongs to the returned allocation, so the mapper may be dropped
/// or reused while an allocation remains alive.
#[derive(Debug)]
pub struct MemoryMapper {
    regions: &'static [MemoryRegion],
}

impl MemoryMapper {
    #[inline]
    pub fn new(regions: Option<&'static [MemoryRegion]>) -> Self {
        Self {
            regions: regions.unwrap_or(&[]),
        }
    }

    fn fixed_region(&self, start: usize, len: usize) -> LoadResult<&'static MemoryRegion> {
        let context = || ErrorContext::TargetRange {
            start: TargetAddress::new(start as u64),
            len: len as u64,
            align: 1,
        };
        let end = start
            .checked_add(len)
            .ok_or_else(|| LoadError::new(LoadErrorKind::IntegerOverflow, context()))?;
        let requested = MemoryPermissions::READ.bitor(MemoryPermissions::WRITE);
        let mut in_bounds = false;
        for region in self.regions {
            if region.start < region.end && start >= region.start && end <= region.end {
                in_bounds = true;
                if region.permissions.contains(requested) {
                    return Ok(region);
                }
            }
        }
        Err(LoadError::new(
            if in_bounds {
                LoadErrorKind::PermissionConflict
            } else {
                LoadErrorKind::OutOfBounds
            },
            context(),
        ))
    }
}

#[derive(Debug)]
#[must_use = "retain the backing until its allocation is released"]
enum FlatBacking {
    Owned(Storage),
    Fixed(&'static MemoryRegion),
}

/// Owns heap backing or the exclusive use of one fixed region.
///
/// Dropping owned backing frees it. Dropping fixed backing only releases the
/// region claim; it does not restore bytes. The next preparation clears its
/// requested span before returning another allocation.
#[derive(Debug)]
#[must_use = "keep the allocation alive while its image is in use"]
pub struct FlatImageAllocation {
    backing: FlatBacking,
    base: TargetAddress,
    len: u64,
    align: u64,
}

impl Drop for FlatImageAllocation {
    fn drop(&mut self) {
        if let FlatBacking::Fixed(region) = &self.backing {
            region.occupied.store(false, Ordering::Release);
        }
        // Owned Storage is released by its own Drop after this method.
    }
}

impl FlatImageAllocation {
    fn image_span(&self, offset: AllocationOffset, len: u64) -> LoadResult<*mut u8> {
        let end = offset
            .value()
            .checked_add(len)
            .filter(|end| *end <= self.len)
            .ok_or_else(|| memory_access_error(self, offset, len))?;
        let offset_usize =
            usize::try_from(offset.value()).map_err(|_| memory_access_error(self, offset, len))?;
        let end = usize::try_from(end).map_err(|_| memory_access_error(self, offset, len))?;
        match &self.backing {
            FlatBacking::Owned(storage) => {
                let base = storage.base();
                if base.is_null() || storage.size() < end {
                    return Err(memory_access_error(self, offset, len));
                }
                // SAFETY: the span is within this allocation's live Storage;
                // an empty access may start one-past its end.
                Ok(unsafe { base.add(offset_usize) })
            }
            FlatBacking::Fixed(_) => {
                let base = usize::try_from(self.base.get())
                    .map_err(|_| memory_access_error(self, offset, len))?;
                let address = base
                    .checked_add(offset_usize)
                    .ok_or_else(|| memory_access_error(self, offset, len))?;
                Ok(address as *mut u8)
            }
        }
    }
}

impl ImageMemory for MemoryMapper {
    type Allocation = FlatImageAllocation;

    fn prepare_image(&mut self, layout: &ImageLayout) -> LoadResult<Self::Allocation> {
        let size = usize::try_from(layout.size()).map_err(|_| allocation_error(layout))?;
        let align = usize::try_from(layout.align()).map_err(|_| allocation_error(layout))?;
        let (backing, base) = match layout.placement() {
            Placement::Anywhere => {
                let storage_layout =
                    Layout::from_size_align(size, align).map_err(|_| allocation_error(layout))?;
                let storage = Storage::try_from_layout(storage_layout).ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::OutOfMemory,
                        ErrorContext::Allocation {
                            base: TargetAddress::new(0),
                            len: layout.size(),
                            align: layout.align(),
                        },
                    )
                })?;
                let base = TargetAddress::new(storage.base() as usize as u64);
                (FlatBacking::Owned(storage), base)
            }
            Placement::Fixed(range) => {
                let start =
                    usize::try_from(range.start().get()).map_err(|_| allocation_error(layout))?;
                // Validate access before acquiring the region or modifying bytes.
                let region = self.fixed_region(start, size)?;
                region
                    .occupied
                    .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                    .map_err(|_| allocation_error(layout))?;
                (FlatBacking::Fixed(region), range.start())
            }
        };
        // Cleanup is already owned before any subsequent operation can fail.
        let mut allocation = FlatImageAllocation {
            backing,
            base,
            len: layout.size(),
            align: layout.align(),
        };
        // Initialize the complete flat span, including holes, before safe reads.
        // Fixed storage is a disposable loading workspace, not an old image to restore.
        allocation.zero(AllocationOffset::new(0), layout.size())?;
        Ok(allocation)
    }
}

impl ImageMapping for FlatImageAllocation {
    fn base(&self) -> TargetAddress {
        self.base
    }

    fn len(&self) -> u64 {
        self.len
    }

    fn align(&self) -> u64 {
        self.align
    }

    fn read(&self, offset: AllocationOffset, dst: &mut [u8]) -> LoadResult<()> {
        let len =
            u64::try_from(dst.len()).map_err(|_| memory_access_error(self, offset, u64::MAX))?;
        let source = self.image_span(offset, len)?;
        if !dst.is_empty() {
            // SAFETY: checked initialized backing remains owned or exclusively
            // borrowed by self; dst is a disjoint exclusive slice.
            unsafe { core::ptr::copy_nonoverlapping(source, dst.as_mut_ptr(), dst.len()) };
        }
        Ok(())
    }

    fn write(&mut self, offset: AllocationOffset, data: &[u8]) -> LoadResult<()> {
        let len =
            u64::try_from(data.len()).map_err(|_| memory_access_error(self, offset, u64::MAX))?;
        let target = self.image_span(offset, len)?;
        if !data.is_empty() {
            // SAFETY: the checked target is exclusively owned or borrowed by self
            // and does not overlap the readable input slice.
            unsafe { core::ptr::copy_nonoverlapping(data.as_ptr(), target, data.len()) };
        }
        Ok(())
    }

    fn zero(&mut self, offset: AllocationOffset, len: u64) -> LoadResult<()> {
        let target = self.image_span(offset, len)?;
        let count = usize::try_from(len).map_err(|_| memory_access_error(self, offset, len))?;
        if count != 0 {
            // SAFETY: image_span checked the exclusively owned/borrowed range.
            unsafe { core::ptr::write_bytes(target, 0, count) };
        }
        Ok(())
    }
}

fn allocation_error(layout: &ImageLayout) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: TargetAddress::new(0),
            len: layout.size(),
            align: layout.align(),
        },
    )
}

fn memory_access_error(
    allocation: &FlatImageAllocation,
    offset: AllocationOffset,
    len: u64,
) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::MemoryAccess {
            allocation_base: allocation.base,
            allocation_len: allocation.len,
            allocation_align: allocation.align,
            offset: offset.value(),
            len,
        },
    )
}
