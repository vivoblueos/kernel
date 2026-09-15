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

use alloc::vec::Vec;

use crate::{
    address::{TargetAddress, TargetRange},
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult},
    MemoryPermissions,
};

/// Where an image wants its memory to come from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement {
    /// Any suitably aligned address (ET_DYN images).
    Anywhere,
    /// Exactly this virtual range (ET_EXEC images).
    Fixed(TargetRange),
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AllocationId(u64);

impl AllocationId {
    #[inline]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    #[inline]
    pub const fn value(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AllocationOwnership {
    Owned,
    BorrowedFixed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AllocationRequest {
    placement: Placement,
    size: u64,
    align: u64,
}

impl AllocationRequest {
    #[inline]
    pub const fn new(placement: Placement, size: u64, align: u64) -> Self {
        Self {
            placement,
            size,
            align,
        }
    }

    #[inline]
    pub const fn placement(&self) -> Placement {
        self.placement
    }

    #[inline]
    pub const fn size(&self) -> u64 {
        self.size
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        self.align
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ImageAllocation {
    id: AllocationId,
    base: TargetAddress,
    len: u64,
    align: u64,
    ownership: AllocationOwnership,
}

impl ImageAllocation {
    #[inline]
    pub const fn new(base: TargetAddress, len: u64, align: u64) -> Self {
        Self::with_identity(
            AllocationId::new(0),
            base,
            len,
            align,
            AllocationOwnership::Owned,
        )
    }

    #[inline]
    pub const fn with_identity(
        id: AllocationId,
        base: TargetAddress,
        len: u64,
        align: u64,
        ownership: AllocationOwnership,
    ) -> Self {
        Self {
            id,
            base,
            len,
            align,
            ownership,
        }
    }

    #[inline]
    pub const fn id(&self) -> AllocationId {
        self.id
    }

    #[inline]
    pub const fn base(&self) -> TargetAddress {
        self.base
    }

    #[inline]
    pub const fn len(&self) -> u64 {
        self.len
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        self.align
    }

    #[inline]
    pub const fn ownership(&self) -> AllocationOwnership {
        self.ownership
    }
}

/// The unique authority to abort or commit one image allocation.
///
/// Backends create a lease together with the allocation they record. The
/// loader never clones a lease and transfers it exactly once: either back to
/// the backend on abort, or into the backend's committed owner.
#[must_use = "allocation lease must be transferred or aborted exactly once"]
#[derive(Debug)]
pub struct AllocationLease {
    allocation: ImageAllocation,
}

impl AllocationLease {
    /// Create the unique authority for an allocation recorded by a backend.
    ///
    /// # Safety
    ///
    /// The caller must be the backend that just created `allocation`, must
    /// have validated and recorded the complete descriptor, and must ensure no
    /// other live `AllocationLease` exists for the same backend allocation.
    /// The lease must subsequently be accepted exactly once by that backend's
    /// abort, commit, or release path.
    #[inline]
    pub const unsafe fn new(allocation: ImageAllocation) -> Self {
        Self { allocation }
    }

    #[inline]
    pub const fn allocation(&self) -> &ImageAllocation {
        &self.allocation
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum MutationProgress {
    Reserved,
    BytesModified,
    ProtectionModified,
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
pub struct AllocationOffset(u64);

impl AllocationOffset {
    #[inline]
    pub const fn new(offset: u64) -> Self {
        Self(offset)
    }

    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }

    pub fn checked_add(self, value: u64) -> LoadResult<Self> {
        let offset = self.0.checked_add(value).ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::MemoryAccess {
                    allocation_base: TargetAddress::new(0),
                    allocation_len: 0,
                    allocation_align: 0,
                    offset: self.0,
                    len: value,
                },
            )
        })?;
        Ok(Self::new(offset))
    }
}

/// Memory backend contract for one or more concurrently live image
/// allocations.
///
/// Every data access explicitly names the allocation it targets. A backend
/// must validate the complete descriptor against its own bookkeeping
/// (identifier, base, length, alignment and ownership) before serving the
/// access; it must not maintain a "current allocation" side channel.
/// `MemoryMapper` keeps at most one active allocation and rejects any
/// descriptor that does not match it; multi-image backends key allocations by
/// `AllocationId` and may serve many at once.
pub trait ImageMemory {
    /// Allocate or borrow exactly the logical range requested by the loader.
    /// Returning `Err` must leave no allocation behind. On success the
    /// backend returns the unique allocation lease; the loader transfers it
    /// back through `abort_image` or into the committed owner through
    /// `ImageCommitMemory::commit_install`.
    fn allocate_image(&mut self, request: AllocationRequest) -> LoadResult<AllocationLease>;

    /// Abort an uncommitted image. This operation must not allocate, fail or
    /// panic. Modified borrowed-fixed ranges must become poisoned.
    fn abort_image(&mut self, allocation: AllocationLease, progress: MutationProgress);

    /// Release a successfully committed image when its owner ends its
    /// lifetime. Borrowed-fixed contents are not restored or poisoned.
    fn release_committed(&mut self, allocation: AllocationLease);

    /// Return a host pointer covering `allocation[offset..offset+len]`.
    /// The descriptor must name an allocation this backend currently
    /// tracks; otherwise an error is returned.
    fn image_span(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<*mut u8>;

    fn write(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        data: &[u8],
    ) -> LoadResult<()>;

    fn zero(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<()>;

    fn read(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        dst: &mut [u8],
    ) -> LoadResult<()>;
}

pub trait ImageProtectionMemory: ImageMemory {
    fn protect(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
        permissions: MemoryPermissions,
    ) -> LoadResult<crate::image::ProtectionLevel>;

    fn protection_capabilities(&self) -> crate::image::ProtectionCapabilities;

    fn validate_protection_aliases(
        &self,
        allocation: &ImageAllocation,
        prepared: &crate::image::PreparedProtectionPlan,
    ) -> LoadResult<()>;

    fn apply_protection(
        &mut self,
        allocation: &ImageAllocation,
        mut batch: crate::image::ProtectionBatch<'_>,
    ) -> LoadResult<()> {
        for index in 0..batch.records().len() {
            let record = batch.records()[index];
            let level = self.protect(
                allocation,
                record.allocation_offset(),
                record.applied_range().len(),
                record.permissions(),
            )?;
            let _ = batch.record_level(index, level);
        }
        Ok(())
    }
}

/// Backend side of the local two-phase install protocol.
///
/// `prepare_install` performs every fallible validation and constructs all
/// state needed for publication. `commit_install` may only move that prepared
/// state and the unique lease into the committed owner.
pub trait ImageCommitMemory: ImageProtectionMemory {
    type PreparedInstall;
    type CommitReceipt;

    fn prepare_install(
        &mut self,
        allocation: &ImageAllocation,
        sealed: &crate::SealedState,
    ) -> LoadResult<Self::PreparedInstall>;

    /// # Safety
    ///
    /// `prepared`, `sealed`, and `lease` must come from the same active load
    /// transaction on this backend. Implementations must not allocate,
    /// validate, panic, or otherwise fail.
    unsafe fn commit_install(
        &mut self,
        prepared: Self::PreparedInstall,
        sealed: crate::SealedState,
        lease: AllocationLease,
    ) -> Self::CommitReceipt;
}

/// Stable reference to one allocation whose unique lease is owned by a
/// session rollback log.
///
/// This value is intentionally copyable: it can select an image for reads,
/// relocation and protection, but it has no authority to abort, commit or
/// release the allocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SessionAllocation {
    slot: RollbackSlot,
    allocation: ImageAllocation,
}

impl SessionAllocation {
    #[inline]
    pub(crate) const fn allocation(self) -> ImageAllocation {
        self.allocation
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RollbackSlot(usize);

#[derive(Debug)]
struct AllocationRollbackEntry {
    lease: AllocationLease,
    progress: MutationProgress,
}

/// Unique rollback authority for the image allocations absorbed by a future
/// multi-image link session.
///
/// The owning session must keep this log beside the exact memory backend from
/// which the transactions were created. While the session is active, its
/// `Drop` implementation calls `abort_all` on that backend. A later batch
/// commit will instead drain the same entries into the committed owner.
#[must_use = "an active allocation rollback log must be aborted or committed"]
pub(crate) struct AllocationRollbackLog {
    entries: Vec<AllocationRollbackEntry>,
}

impl AllocationRollbackLog {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Reserve a slot while the source transaction is still armed. If this
    /// fails, the transaction remains the lease owner and its Drop aborts the
    /// allocation.
    fn reserve_entry(&mut self) -> LoadResult<()> {
        self.entries
            .try_reserve(1)
            .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))
    }

    /// Insert into the slot reserved immediately before this call. No
    /// allocation or user-defined code is executed between taking the lease
    /// from the transaction and storing it here.
    fn push_reserved(
        &mut self,
        lease: AllocationLease,
        progress: MutationProgress,
    ) -> SessionAllocation {
        let slot = RollbackSlot(self.entries.len());
        let allocation = *lease.allocation();
        self.entries
            .push(AllocationRollbackEntry { lease, progress });
        SessionAllocation { slot, allocation }
    }

    fn entry_mut(
        &mut self,
        allocation: SessionAllocation,
    ) -> LoadResult<&mut AllocationRollbackEntry> {
        let entry = self
            .entries
            .get_mut(allocation.slot.0)
            .ok_or_else(|| session_allocation_error(allocation.allocation))?;
        if entry.lease.allocation() != &allocation.allocation {
            return Err(session_allocation_error(allocation.allocation));
        }
        Ok(entry)
    }

    /// Record a later session write before invoking the backend, preserving
    /// conservative rollback semantics if that write partially succeeds.
    pub(crate) fn mark_bytes_modified(&mut self, allocation: SessionAllocation) -> LoadResult<()> {
        let entry = self.entry_mut(allocation)?;
        entry.progress = core::cmp::max(entry.progress, MutationProgress::BytesModified);
        Ok(())
    }

    /// Record a later session protection mutation before invoking the
    /// backend.
    pub(crate) fn mark_protection_modified(
        &mut self,
        allocation: SessionAllocation,
    ) -> LoadResult<()> {
        self.entry_mut(allocation)?.progress = MutationProgress::ProtectionModified;
        Ok(())
    }

    /// Abort every absorbed allocation in reverse creation order. This
    /// operation performs no allocation and leaves the log empty.
    pub(crate) fn abort_all<M: ImageMemory + ?Sized>(&mut self, memory: &mut M) {
        while let Some(entry) = self.entries.pop() {
            memory.abort_image(entry.lease, entry.progress);
        }
    }

    /// Number of absorbed allocations.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Move every absorbed lease out of the log in creation order, leaving it
    /// empty. `sink` must already hold `len()` spare capacity so this cannot
    /// allocate; the publication commit uses it to transfer the unique leases
    /// into the publisher's committed owner without a fallible step.
    pub(crate) fn drain_leases_into(&mut self, sink: &mut Vec<AllocationLease>) {
        for entry in self.entries.drain(..) {
            sink.push(entry.lease);
        }
    }
}

fn session_allocation_error(allocation: ImageAllocation) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base: allocation.base(),
            len: allocation.len(),
            align: allocation.align(),
        },
    )
}

#[must_use = "dropping an active image transaction aborts its allocation"]
pub(crate) struct ImageLoadTransaction<M: ImageMemory> {
    memory: M,
    pending: Option<AllocationLease>,
    progress: MutationProgress,
}

impl<M: ImageMemory> ImageLoadTransaction<M> {
    #[inline]
    pub(crate) const fn new(memory: M, lease: AllocationLease) -> Self {
        Self {
            memory,
            pending: Some(lease),
            progress: MutationProgress::Reserved,
        }
    }

    #[inline]
    pub(crate) fn allocation(&self) -> &ImageAllocation {
        self.pending
            .as_ref()
            .expect("active image transaction must own its lease")
            .allocation()
    }

    #[inline]
    pub(crate) fn memory_mut(&mut self) -> &mut M {
        &mut self.memory
    }

    #[inline]
    fn mark_bytes_modified(&mut self) {
        self.progress = core::cmp::max(self.progress, MutationProgress::BytesModified);
    }

    #[inline]
    fn mark_protection_modified(&mut self) {
        self.progress = MutationProgress::ProtectionModified;
    }

    #[inline]
    pub(crate) fn take_lease(&mut self) -> AllocationLease {
        self.pending
            .take()
            .expect("ready image transaction must own its lease")
    }

    /// Owner-bound wrapper around `ImageMemory::read` that always passes the
    /// transaction's own allocation descriptor. Bytes modifications must go
    /// through `write`/`zero` so the progress marker stays accurate.
    pub(crate) fn read(&self, offset: AllocationOffset, dst: &mut [u8]) -> LoadResult<()> {
        let allocation = *self.allocation();
        self.memory.read(&allocation, offset, dst)
    }

    /// Owner-bound wrapper around `ImageMemory::write`. Marks the allocation
    /// as bytes-modified before issuing the write so that an abort on error
    /// still observes the modification.
    pub(crate) fn write(&mut self, offset: AllocationOffset, src: &[u8]) -> LoadResult<()> {
        let allocation = *self.allocation();
        self.mark_bytes_modified();
        self.memory.write(&allocation, offset, src)
    }

    /// Owner-bound wrapper around `ImageMemory::zero`. Marks the allocation
    /// as bytes-modified before issuing the zero fill.
    pub(crate) fn zero(&mut self, offset: AllocationOffset, len: u64) -> LoadResult<()> {
        let allocation = *self.allocation();
        self.mark_bytes_modified();
        self.memory.zero(&allocation, offset, len)
    }

    /// Owner-bound wrapper around `ImageMemory::image_span`. The returned
    /// pointer borrows the backend; it must not escape the caller.
    pub(crate) fn image_span(&self, offset: AllocationOffset, len: u64) -> LoadResult<*mut u8> {
        let allocation = *self.allocation();
        self.memory.image_span(&allocation, offset, len)
    }
}

impl<M: ImageProtectionMemory> ImageLoadTransaction<M> {
    #[inline]
    pub(crate) fn protection_capabilities(&self) -> crate::image::ProtectionCapabilities {
        self.memory.protection_capabilities()
    }

    pub(crate) fn validate_protection_aliases(
        &self,
        prepared: &crate::image::PreparedProtectionPlan,
    ) -> LoadResult<()> {
        let allocation = *self.allocation();
        self.memory
            .validate_protection_aliases(&allocation, prepared)
    }

    /// Apply the complete protection batch to this transaction's allocation.
    /// Progress is advanced first so partial backend mutation is always
    /// conservatively rolled back.
    pub(crate) fn apply_protection(
        &mut self,
        batch: crate::image::ProtectionBatch<'_>,
    ) -> LoadResult<()> {
        let allocation = *self.allocation();
        self.mark_protection_modified();
        self.memory.apply_protection(&allocation, batch)
    }
}

impl<M: ImageMemory + ?Sized> ImageLoadTransaction<&mut M> {
    /// Transfer this transaction's unique lease directly into a pre-reserved
    /// session rollback slot.
    ///
    /// Slot reservation happens while the transaction is still armed. On
    /// allocation failure `self` drops normally and aborts the image; after
    /// reservation, moving the lease into the log is infallible. Consuming
    /// `self` also ends the short mutable reborrow of the session backend.
    pub(crate) fn transfer_to(
        mut self,
        rollback: &mut AllocationRollbackLog,
    ) -> LoadResult<SessionAllocation> {
        rollback.reserve_entry()?;
        debug_assert!(rollback.entries.len() < rollback.entries.capacity());
        let lease = self
            .pending
            .take()
            .expect("active image transaction must own its lease");
        Ok(rollback.push_reserved(lease, self.progress))
    }
}

impl<M: ImageMemory> Drop for ImageLoadTransaction<M> {
    fn drop(&mut self) {
        if let Some(lease) = self.pending.take() {
            self.memory.abort_image(lease, self.progress);
        }
    }
}

impl<M: ImageMemory + ?Sized> ImageMemory for &mut M {
    fn allocate_image(&mut self, request: AllocationRequest) -> LoadResult<AllocationLease> {
        (**self).allocate_image(request)
    }

    fn abort_image(&mut self, allocation: AllocationLease, progress: MutationProgress) {
        (**self).abort_image(allocation, progress)
    }

    fn release_committed(&mut self, allocation: AllocationLease) {
        (**self).release_committed(allocation)
    }

    fn image_span(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<*mut u8> {
        (**self).image_span(allocation, offset, len)
    }

    fn write(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        data: &[u8],
    ) -> LoadResult<()> {
        (**self).write(allocation, offset, data)
    }

    fn zero(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
    ) -> LoadResult<()> {
        (**self).zero(allocation, offset, len)
    }

    fn read(
        &self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        dst: &mut [u8],
    ) -> LoadResult<()> {
        (**self).read(allocation, offset, dst)
    }
}

impl<M: ImageProtectionMemory + ?Sized> ImageProtectionMemory for &mut M {
    fn protect(
        &mut self,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        len: u64,
        permissions: MemoryPermissions,
    ) -> LoadResult<crate::image::ProtectionLevel> {
        (**self).protect(allocation, offset, len, permissions)
    }

    fn protection_capabilities(&self) -> crate::image::ProtectionCapabilities {
        (**self).protection_capabilities()
    }

    fn validate_protection_aliases(
        &self,
        allocation: &ImageAllocation,
        prepared: &crate::image::PreparedProtectionPlan,
    ) -> LoadResult<()> {
        (**self).validate_protection_aliases(allocation, prepared)
    }

    fn apply_protection(
        &mut self,
        allocation: &ImageAllocation,
        batch: crate::image::ProtectionBatch<'_>,
    ) -> LoadResult<()> {
        (**self).apply_protection(allocation, batch)
    }
}
