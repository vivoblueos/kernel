// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use blueos_infra::storage::Storage;
use core::alloc::Layout;

use crate::{
    address::TargetAddress,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult},
    image::{PreparedProtectionPlan, ProtectionCapabilities, ProtectionLevel},
    memory::{
        AllocationId, AllocationLease, AllocationOffset, AllocationOwnership, AllocationRequest,
        ImageAllocation, ImageCommitMemory, ImageMemory, ImageProtectionMemory, MutationProgress,
        Placement,
    },
    SealedState,
};

pub type Result<T> = core::result::Result<T, &'static str>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoryPermissions(u8);

impl MemoryPermissions {
    pub const NONE: Self = Self(0);
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXECUTE: Self = Self(1 << 2);

    pub const fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }

    pub(crate) const fn without(self, removed: Self) -> Self {
        Self(self.0 & !removed.0)
    }

    pub const fn contains(self, requested: Self) -> bool {
        self.0 & requested.0 == requested.0
    }

    #[inline]
    pub const fn bits(self) -> u8 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoryRegion {
    start: usize,
    end: usize,
    permissions: MemoryPermissions,
}

impl MemoryRegion {
    /// Authorizes a fixed address range for accesses described by `permissions`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `[start, end)` is a valid mapped range for every
    /// advertised permission and remains so for the lifetime of any mapper that uses
    /// this region. While a mapper accesses the range, it must not alias Rust references
    /// or receive conflicting accesses.
    pub const unsafe fn new(start: usize, end: usize, permissions: MemoryPermissions) -> Self {
        Self {
            start,
            end,
            permissions,
        }
    }
}

#[derive(Debug)]
pub(crate) enum MappingMode {
    Allocated,
    Fixed(&'static [MemoryRegion]),
}

#[derive(Debug)]
pub struct MemoryMapper {
    virtual_entry: usize,
    real_entry: usize,
    mem: Storage,
    mode: MappingMode,
    allocation: Option<ImageAllocation>,
    installed: Option<MemoryMapperInstalledImage>,
    poisoned: Option<ImageAllocation>,
    next_allocation_id: u64,
}

#[derive(Debug)]
pub struct MemoryMapperPreparedInstall {
    allocation: ImageAllocation,
    virtual_entry: usize,
    real_entry: usize,
}

#[derive(Debug)]
struct MemoryMapperInstalledImage {
    lease: AllocationLease,
}

/// Compatibility receipt. The mapper's installed state, rather than this
/// value, owns the allocation lease.
#[derive(Debug)]
pub struct MemoryMapperCommitReceipt {
    _private: (),
}

impl MemoryMapper {
    #[inline]
    pub fn new(regions: Option<&'static [MemoryRegion]>) -> Self {
        Self {
            virtual_entry: 0,
            real_entry: 0,
            mem: Storage::default(),
            mode: match regions {
                Some(regions) => MappingMode::Fixed(regions),
                None => MappingMode::Allocated,
            },
            allocation: None,
            installed: None,
            poisoned: None,
            next_allocation_id: 1,
        }
    }

    #[inline]
    pub(crate) fn mapping_mode(&self) -> &MappingMode {
        &self.mode
    }

    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned.is_some()
    }

    /// Clear the fixed-image poison marker after the platform has restored or
    /// reinitialized the recorded range.
    ///
    /// # Safety
    ///
    /// The caller must ensure that no code can execute from the poisoned
    /// range and that its contents/protection state are safe for a new load.
    pub unsafe fn reset_poisoned(&mut self) {
        self.poisoned = None;
    }

    #[inline]
    pub fn entry(&self) -> usize {
        self.virtual_entry
    }

    #[inline]
    pub fn real_entry(&self) -> Result<usize> {
        if self.installed.is_none() {
            return Err("Image has not been committed");
        }
        Ok(self.real_entry)
    }

    pub(crate) fn validate_fixed_span(
        &self,
        start: usize,
        size: usize,
        requested: MemoryPermissions,
    ) -> Result<()> {
        let MappingMode::Fixed(regions) = &self.mode else {
            return Err("Fixed span requires a fixed mapper");
        };
        let end = start
            .checked_add(size)
            .ok_or("Address span overflows the target address space")?;
        let valid = regions.iter().any(|region| {
            region.start < region.end
                && start >= region.start
                && end <= region.end
                && region.permissions.contains(requested)
        });
        if valid {
            Ok(())
        } else {
            Err("Address span is outside authorized regions")
        }
    }

    fn clear_installed_addresses(&mut self) {
        self.virtual_entry = 0;
        self.real_entry = 0;
    }

    fn next_allocation_id(&mut self, request: &AllocationRequest) -> LoadResult<AllocationId> {
        let id = self.next_allocation_id;
        self.next_allocation_id = self
            .next_allocation_id
            .checked_add(1)
            .ok_or_else(|| allocation_error(request))?;
        Ok(AllocationId::new(id))
    }

    fn create_allocation(
        &mut self,
        request: &AllocationRequest,
        base: TargetAddress,
        ownership: AllocationOwnership,
    ) -> LoadResult<(ImageAllocation, AllocationLease)> {
        let allocation = ImageAllocation::with_identity(
            self.next_allocation_id(request)?,
            base,
            request.size(),
            request.align(),
            ownership,
        );
        // SAFETY: this mapper has just recorded `allocation` as its sole
        // active allocation and cannot mint another lease until it is
        // aborted, committed, or released.
        let lease = unsafe { AllocationLease::new(allocation) };
        Ok((allocation, lease))
    }

    fn release_lease(&mut self, lease: AllocationLease, poison: bool) {
        let allocation = *lease.allocation();
        if self.allocation != Some(allocation) {
            return;
        }

        self.clear_installed_addresses();
        self.allocation = None;
        match allocation.ownership() {
            AllocationOwnership::Owned => self.mem = Storage::default(),
            AllocationOwnership::BorrowedFixed if poison => {
                self.poisoned = Some(allocation);
            }
            AllocationOwnership::BorrowedFixed => {}
        }
    }
}

impl MemoryMapper {
    /// Validate that `descriptor` matches the mapper's currently tracked
    /// allocation. `MemoryMapper` keeps at most one active allocation; any
    /// mismatch — including a stale descriptor from a finished load — is an
    /// error rather than a silent redirect.
    fn expect_active_allocation(
        &self,
        descriptor: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<()> {
        match &self.allocation {
            Some(active) if active == descriptor => Ok(()),
            Some(_) => Err(memory_access_error(*descriptor, offset, len)),
            None => Err(not_allocated_error(*descriptor)),
        }
    }
}

impl ImageMemory for MemoryMapper {
    fn allocate_image(&mut self, request: AllocationRequest) -> LoadResult<AllocationLease> {
        if self.poisoned.is_some() || self.installed.is_some() || self.allocation.is_some() {
            return Err(allocation_error(&request));
        }
        match (&self.mode, request.placement()) {
            (MappingMode::Allocated, Placement::Anywhere) => {
                if !self.mem.base().is_null() {
                    return Err(allocation_error(&request));
                }

                let size =
                    usize::try_from(request.size()).map_err(|_| allocation_error(&request))?;
                let align =
                    usize::try_from(request.align()).map_err(|_| allocation_error(&request))?;
                if size == 0 {
                    return Err(allocation_error(&request));
                }
                let layout =
                    Layout::from_size_align(size, align).map_err(|_| allocation_error(&request))?;

                let storage = Storage::try_from_layout(layout).ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::OutOfMemory,
                        ErrorContext::Allocation {
                            base: TargetAddress::new(0),
                            len: request.size(),
                            align: request.align(),
                        },
                    )
                })?;
                let base = TargetAddress::new(
                    u64::try_from(storage.base() as usize)
                        .map_err(|_| allocation_error(&request))?,
                );
                let (allocation, lease) =
                    self.create_allocation(&request, base, AllocationOwnership::Owned)?;
                self.mem = storage;
                self.allocation = Some(allocation);
                Ok(lease)
            }
            // A fixed image borrows its span from the mapper's static
            // regions: validate the whole span before recording anything, and
            // never touch the heap storage.
            (MappingMode::Fixed(_), Placement::Fixed(range)) => {
                let start =
                    usize::try_from(range.start().get()).map_err(|_| allocation_error(&request))?;
                let len = usize::try_from(range.len()).map_err(|_| allocation_error(&request))?;
                self.validate_fixed_span(start, len, MemoryPermissions::NONE)
                    .map_err(|_| allocation_error(&request))?;
                let (allocation, lease) = self.create_allocation(
                    &request,
                    range.start(),
                    AllocationOwnership::BorrowedFixed,
                )?;
                self.allocation = Some(allocation);
                Ok(lease)
            }
            _ => Err(allocation_error(&request)),
        }
    }

    fn abort_image(&mut self, allocation: AllocationLease, progress: MutationProgress) {
        let poison = allocation.allocation().ownership() == AllocationOwnership::BorrowedFixed
            && progress != MutationProgress::Reserved;
        self.release_lease(allocation, poison);
    }

    fn release_committed(&mut self, allocation: AllocationLease) {
        self.release_lease(allocation, false);
    }

    fn image_span(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<*mut u8> {
        self.expect_active_allocation(allocation, offset, len)?;
        let end = offset
            .value()
            .checked_add(len)
            .filter(|end| *end <= allocation.len())
            .ok_or_else(|| memory_access_error(*allocation, offset, len))?;
        let offset_usize = usize::try_from(offset.value())
            .map_err(|_| memory_access_error(*allocation, offset, len))?;
        let end =
            usize::try_from(end).map_err(|_| memory_access_error(*allocation, offset, len))?;
        match &self.mode {
            MappingMode::Allocated => {
                let base = self.mem.base();
                if base.is_null() || self.mem.size() < end {
                    return Err(memory_access_error(*allocation, offset, len));
                };
                Ok(unsafe { base.add(offset_usize) })
            }
            // Fixed images already validated their span against the static
            // regions at allocation time; the offset bounds check above keeps
            // accesses inside the recorded allocation.
            MappingMode::Fixed(_) => {
                let base = usize::try_from(allocation.base().get())
                    .map_err(|_| memory_access_error(*allocation, offset, len))?;
                let address = base
                    .checked_add(offset_usize)
                    .ok_or_else(|| memory_access_error(*allocation, offset, len))?;
                Ok(address as *mut u8)
            }
        }
    }

    fn read(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        dst: &mut [u8],
    ) -> LoadResult<()> {
        let len = u64::try_from(dst.len())
            .map_err(|_| memory_access_error(*allocation, offset, u64::MAX))?;
        let source = self.image_span(allocation, offset, len)?;
        if !dst.is_empty() {
            unsafe {
                core::ptr::copy_nonoverlapping(source, dst.as_mut_ptr(), dst.len());
            }
        }
        Ok(())
    }

    fn write(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        data: &[u8],
    ) -> LoadResult<()> {
        let len = u64::try_from(data.len())
            .map_err(|_| memory_access_error(*allocation, offset, u64::MAX))?;
        let target = self.image_span(allocation, offset, len)?;
        if !data.is_empty() {
            unsafe {
                core::ptr::copy_nonoverlapping(data.as_ptr(), target, data.len());
            }
        }
        Ok(())
    }

    fn zero(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<()> {
        let target = self.image_span(allocation, offset, len)?;
        let len =
            usize::try_from(len).map_err(|_| memory_access_error(*allocation, offset, len))?;
        if len != 0 {
            unsafe {
                core::ptr::write_bytes(target, 0, len);
            }
        }
        Ok(())
    }
}

impl ImageProtectionMemory for MemoryMapper {
    fn protect(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
        _permissions: MemoryPermissions,
    ) -> LoadResult<ProtectionLevel> {
        self.image_span(allocation, offset, len)?;
        Ok(ProtectionLevel::LogicalOnly)
    }

    fn protection_capabilities(&self) -> ProtectionCapabilities {
        ProtectionCapabilities::new(1, usize::MAX)
    }

    fn validate_protection_aliases(
        &self,
        allocation: &ImageAllocation,
        _prepared: &PreparedProtectionPlan,
    ) -> LoadResult<()> {
        match &self.allocation {
            Some(actual) if actual == allocation => Ok(()),
            _ => Err(protection_backend_error(allocation)),
        }
    }
}

impl ImageCommitMemory for MemoryMapper {
    type PreparedInstall = MemoryMapperPreparedInstall;
    type CommitReceipt = MemoryMapperCommitReceipt;

    fn prepare_install(
        &mut self,
        allocation: &ImageAllocation,
        sealed: &SealedState,
    ) -> LoadResult<Self::PreparedInstall> {
        let mismatch = match &self.allocation {
            Some(actual) => actual != allocation,
            None => true,
        };
        if mismatch || self.installed.is_some() || self.poisoned.is_some() {
            return Err(compatibility_install_error(*allocation));
        }

        let virtual_start = allocation.base().checked_sub(sealed.load_bias())?;
        let virtual_end = TargetAddress::new(virtual_start).checked_add(allocation.len())?;
        let virtual_entry = sealed.entry().checked_sub(sealed.load_bias())?;
        usize::try_from(virtual_start).map_err(|_| compatibility_install_error(*allocation))?;
        usize::try_from(virtual_end.get()).map_err(|_| compatibility_install_error(*allocation))?;
        let virtual_entry =
            usize::try_from(virtual_entry).map_err(|_| compatibility_install_error(*allocation))?;

        let canonical_offset = sealed.canonical_entry().checked_sub(allocation.base())?;
        canonical_offset
            .checked_add(1)
            .filter(|end| *end <= allocation.len())
            .ok_or_else(|| compatibility_install_error(*allocation))?;

        let real_entry = match &self.mode {
            MappingMode::Allocated => {
                let entry_offset = sealed.entry().checked_sub(allocation.base())?;
                let entry_offset = usize::try_from(entry_offset)
                    .map_err(|_| compatibility_install_error(*allocation))?;
                let base = self.mem.base();
                if base.is_null() || entry_offset >= self.mem.size() {
                    return Err(compatibility_install_error(*allocation));
                }
                unsafe { base.add(entry_offset) as usize }
            }
            MappingMode::Fixed(_) => {
                let entry = usize::try_from(sealed.entry().get())
                    .map_err(|_| compatibility_install_error(*allocation))?;
                let canonical_entry = usize::try_from(sealed.canonical_entry().get())
                    .map_err(|_| compatibility_install_error(*allocation))?;
                self.validate_fixed_span(canonical_entry, 1, MemoryPermissions::EXECUTE)
                    .map_err(|_| compatibility_install_error(*allocation))?;
                entry
            }
        };

        Ok(MemoryMapperPreparedInstall {
            allocation: *allocation,
            virtual_entry,
            real_entry,
        })
    }

    unsafe fn commit_install(
        &mut self,
        prepared: Self::PreparedInstall,
        _sealed: SealedState,
        lease: AllocationLease,
    ) -> Self::CommitReceipt {
        self.virtual_entry = prepared.virtual_entry;
        self.real_entry = prepared.real_entry;
        self.allocation = Some(prepared.allocation);
        self.installed = Some(MemoryMapperInstalledImage { lease });
        MemoryMapperCommitReceipt { _private: () }
    }
}

impl Drop for MemoryMapper {
    fn drop(&mut self) {
        if let Some(installed) = self.installed.take() {
            self.release_committed(installed.lease);
        }
    }
}

fn allocation_error(request: &AllocationRequest) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: TargetAddress::new(0),
            len: request.size(),
            align: request.align(),
        },
    )
}

fn memory_access_error(
    allocation: ImageAllocation,
    offset: AllocationOffset,
    len: u64,
) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::MemoryAccess {
            allocation_base: allocation.base(),
            allocation_len: allocation.len(),
            allocation_align: allocation.align(),
            offset: offset.value(),
            len,
        },
    )
}

fn not_allocated_error(allocation: ImageAllocation) -> LoadError {
    LoadError::new(
        LoadErrorKind::NotAllocated,
        ErrorContext::Allocation {
            base: allocation.base(),
            len: allocation.len(),
            align: allocation.align(),
        },
    )
}

fn protection_backend_error(allocation: &ImageAllocation) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: allocation.base(),
            len: allocation.len(),
            align: allocation.align(),
        },
    )
}

fn compatibility_install_error(allocation: ImageAllocation) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: allocation.base(),
            len: allocation.len(),
            align: allocation.align(),
        },
    )
}
