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

//! Shared-flat memory backend for dynamic image loading.
//!
//! [`FlatImageMemory`] is not a per-session backing owner. It is a lightweight
//! handle onto one shared service whose allocation table records every live
//! image allocation. Each link session holds an independent handle (a clone of
//! the same `Arc`) and synchronizes the table only for the duration of a single
//! `ImageMemory` call, never across the whole VFS/link. A reaper reaches the
//! same service through its own handle to release a committed lease exactly
//! once. There is no "current allocation" side channel: every access names the
//! allocation it targets and is validated against the full descriptor.

use alloc::{sync::Arc, vec::Vec};
use core::alloc::Layout;

use blueos_infra::storage::Storage;
use blueos_loader::{
    AllocationId, AllocationLease, AllocationOffset, AllocationOwnership, AllocationRequest,
    ErrorContext, ImageAllocation, ImageMemory, ImageProtectionMemory, LoadError, LoadErrorKind,
    LoadResult, MemoryPermissions, MutationProgress, Placement, PreparedProtectionPlan,
    ProtectionCapabilities, ProtectionLevel, TargetAddress,
};
use spin::Mutex;

/// One live allocation: the stable, non-moving backing storage and the full
/// descriptor it was minted with. `Storage` owns the heap block and frees it on
/// drop, so removing an entry is exactly the release of that image's bytes.
struct FlatAllocationEntry {
    storage: Storage,
    allocation: ImageAllocation,
}

/// Shared allocation table plus the identity nonce and monotonic id counter.
///
/// `nonce` is the service instance address, folded into the high bits of every
/// [`AllocationId`] it mints so ids cannot collide with a second, independently
/// created service. `next_counter` is the low bits, monotonic within a service.
struct FlatMemoryService {
    nonce: u64,
    entries: Vec<FlatAllocationEntry>,
    next_counter: u64,
}

impl FlatMemoryService {
    const fn new() -> Self {
        Self {
            nonce: 0,
            entries: Vec::new(),
            next_counter: 1,
        }
    }

    /// Mint a globally unique allocation id: instance nonce in the high bits,
    /// a per-service counter in the low bits.
    fn mint_id(&mut self) -> LoadResult<AllocationId> {
        let counter = self.next_counter;
        self.next_counter = counter
            .checked_add(1)
            .ok_or_else(|| allocation_error_u64(0, 0))?;
        Ok(AllocationId::new((self.nonce << 32) | counter))
    }

    fn entry(&self, allocation: &ImageAllocation) -> Option<&FlatAllocationEntry> {
        self.entries
            .iter()
            .find(|entry| entry.allocation == *allocation)
    }

    fn entry_index(&self, allocation: &ImageAllocation) -> Option<usize> {
        self.entries
            .iter()
            .position(|entry| entry.allocation == *allocation)
    }
}

/// A cloneable handle onto the shared-flat memory service.
pub struct FlatImageMemory {
    service: Arc<Mutex<FlatMemoryService>>,
}

impl FlatImageMemory {
    /// Create a new shared service and return its first handle.
    ///
    /// The boot path creates exactly one service and keeps a handle alive for
    /// the lifetime of the system so it outlives every committed lease; the
    /// reaper obtains its own `Clone` to release those leases.
    pub fn new() -> Self {
        let service = Arc::new(Mutex::new(FlatMemoryService::new()));
        let nonce = Arc::as_ptr(&service) as *const () as usize as u64;
        service.lock().nonce = nonce;
        Self { service }
    }
}

impl Default for FlatImageMemory {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for FlatImageMemory {
    fn clone(&self) -> Self {
        Self {
            service: Arc::clone(&self.service),
        }
    }
}

impl ImageMemory for FlatImageMemory {
    fn allocate_image(&mut self, request: AllocationRequest) -> LoadResult<AllocationLease> {
        // Thumbv7 dynamic images are movable ET_DYN objects loaded from the
        // shared heap. A fixed placement cannot be honoured against this heap
        // backing and is rejected rather than silently redirected.
        if request.placement() != Placement::Anywhere {
            return Err(allocation_error(&request));
        }
        let size = usize::try_from(request.size()).map_err(|_| allocation_error(&request))?;
        let align = usize::try_from(request.align()).map_err(|_| allocation_error(&request))?;
        if size == 0 {
            return Err(allocation_error(&request));
        }
        let layout =
            Layout::from_size_align(size, align).map_err(|_| allocation_error(&request))?;

        let mut service = self.service.lock();
        // Reserve before allocating so the infallible push below cannot fail
        // after we have taken ownership of a heap block.
        service.entries.try_reserve(1).map_err(|_| {
            LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::Allocation {
                    base: TargetAddress::new(0),
                    len: request.size(),
                    align: request.align(),
                },
            )
        })?;
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
            u64::try_from(storage.base() as usize).map_err(|_| allocation_error(&request))?,
        );
        let allocation = ImageAllocation::with_identity(
            service.mint_id()?,
            base,
            request.size(),
            request.align(),
            AllocationOwnership::Owned,
        );
        service.entries.push(FlatAllocationEntry {
            storage,
            allocation,
        });
        // SAFETY: the backend just recorded `allocation` in the shared table
        // and mints no other lease for it; the caller receives the sole
        // authority to abort, commit, or release this allocation.
        Ok(unsafe { AllocationLease::new(allocation) })
    }

    fn abort_image(&mut self, allocation: AllocationLease, _progress: MutationProgress) {
        // Exactly-once, infallible, no allocation: remove the entry keyed by
        // the full descriptor; a second or stale lease finds nothing.
        let mut service = self.service.lock();
        if let Some(index) = service.entry_index(allocation.allocation()) {
            service.entries.swap_remove(index);
        }
    }

    fn release_committed(&mut self, allocation: AllocationLease) {
        let mut service = self.service.lock();
        if let Some(index) = service.entry_index(allocation.allocation()) {
            service.entries.swap_remove(index);
        }
    }

    fn image_span(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<*mut u8> {
        let service = self.service.lock();
        let entry = service
            .entry(allocation)
            .ok_or_else(|| not_allocated_error(*allocation))?;
        let end = offset
            .value()
            .checked_add(len)
            .filter(|end| *end <= allocation.len())
            .ok_or_else(|| memory_access_error(*allocation, offset, len))?;
        let offset_usize = usize::try_from(offset.value())
            .map_err(|_| memory_access_error(*allocation, offset, len))?;
        let end_usize =
            usize::try_from(end).map_err(|_| memory_access_error(*allocation, offset, len))?;
        let base = entry.storage.base();
        if base.is_null() || entry.storage.size() < end_usize {
            return Err(memory_access_error(*allocation, offset, len));
        }
        Ok(unsafe { base.add(offset_usize) })
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
}

impl ImageProtectionMemory for FlatImageMemory {
    fn protect(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
        _permissions: MemoryPermissions,
    ) -> LoadResult<ProtectionLevel> {
        // The shared flat address space has no per-image hardware protection;
        // protection is a logical record only.
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
        let service = self.service.lock();
        if service.entry(allocation).is_some() {
            Ok(())
        } else {
            Err(protection_backend_error(allocation))
        }
    }
}

fn allocation_error(request: &AllocationRequest) -> LoadError {
    allocation_error_u64(request.size(), request.align())
}

fn allocation_error_u64(len: u64, align: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: TargetAddress::new(0),
            len,
            align,
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
