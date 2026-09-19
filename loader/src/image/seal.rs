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
    cache::CacheSyncOutcome,
    elf::LoadSegmentInfo,
    error::{ErrorContext, LimitKind, LoadError, LoadErrorKind, LoadResult, ProgramHeaderField},
    identity::{ElfClass, SINGLE_IMAGE_LOAD_POLICY},
    image::{inspect::StackKind, map::LoadedRegion, RelocationRecord},
    memory::{
        AllocationOffset, ImageAllocation, ImageLoadTransaction, ImageMemory, ImageProtectionMemory,
    },
    MemoryPermissions,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProtectionLevel {
    HardwareEnforced,
    LogicalOnly,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProtectionCapabilities {
    granule: u64,
    max_ranges: usize,
}

impl ProtectionCapabilities {
    #[inline]
    pub const fn new(granule: u64, max_ranges: usize) -> Self {
        Self {
            granule,
            max_ranges,
        }
    }

    #[inline]
    pub const fn granule(self) -> u64 {
        self.granule
    }

    #[inline]
    pub const fn max_ranges(self) -> usize {
        self.max_ranges
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SealRange {
    allocation_offset: AllocationOffset,
    runtime_range: TargetRange,
    permissions: MemoryPermissions,
}

impl SealRange {
    #[inline]
    pub const fn allocation_offset(&self) -> AllocationOffset {
        self.allocation_offset
    }

    #[inline]
    pub const fn runtime_range(&self) -> TargetRange {
        self.runtime_range
    }

    #[inline]
    pub const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }
}

#[derive(Clone, Debug)]
pub struct SealPlan {
    ranges: Vec<SealRange>,
}

impl SealPlan {
    pub fn ranges(&self) -> &[SealRange] {
        &self.ranges
    }

    pub(crate) fn build(
        allocation: &ImageAllocation,
        load_bias: TargetAddress,
        class: ElfClass,
        load_segments: &[LoadSegmentInfo],
        regions: &[LoadedRegion],
        relro: Option<TargetRange>,
        stack: &StackKind,
        relocations: &[RelocationRecord],
    ) -> LoadResult<Self> {
        if *stack == StackKind::Executable && !SINGLE_IMAGE_LOAD_POLICY.allows_executable_stack() {
            return Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::ExecutableStack,
                    value: 0,
                },
            ));
        }
        if load_segments.len() != regions.len() {
            return Err(protection_backend_error(allocation));
        }
        validate_relocation_targets(class, load_segments, relocations)?;
        validate_relro(load_segments, relro)?;

        let capacity = regions
            .len()
            .checked_mul(4)
            .and_then(|value| value.checked_add(1))
            .ok_or_else(seal_oom)?;
        let mut ranges = Vec::new();
        ranges.try_reserve_exact(capacity).map_err(|_| seal_oom())?;

        let mut allocation_cursor = 0_u64;
        for (segment, region) in load_segments.iter().zip(regions.iter()) {
            validate_region(allocation, load_bias, segment, region)?;
            if region.runtime_range().is_empty() {
                continue;
            }

            let region_offset = region.allocation_offset().value();
            let gap_len = region_offset
                .checked_sub(allocation_cursor)
                .ok_or_else(|| {
                    seal_range_error(region.runtime_range(), LoadErrorKind::OutOfBounds)
                })?;
            append_allocation_range(
                allocation,
                &mut ranges,
                allocation_cursor,
                gap_len,
                MemoryPermissions::NONE,
            )?;

            let source = region.vaddr_range();
            if let Some(relro) = relro.filter(|relro| relro.overlaps(source)) {
                let source_end = source.end()?;
                let relro_end = relro.end()?;
                let overlap_start = core::cmp::max(source.start(), relro.start());
                let overlap_end = core::cmp::min(source_end, relro_end);
                append_region_range(
                    load_bias,
                    region,
                    &mut ranges,
                    source.start(),
                    overlap_start.checked_sub(source.start())?,
                    segment.permissions(),
                )?;
                append_region_range(
                    load_bias,
                    region,
                    &mut ranges,
                    overlap_start,
                    overlap_end.checked_sub(overlap_start)?,
                    segment.permissions().without(MemoryPermissions::WRITE),
                )?;
                append_region_range(
                    load_bias,
                    region,
                    &mut ranges,
                    overlap_end,
                    source_end.checked_sub(overlap_end)?,
                    segment.permissions(),
                )?;
            } else {
                append_region_range(
                    load_bias,
                    region,
                    &mut ranges,
                    source.start(),
                    source.len(),
                    segment.permissions(),
                )?;
            }

            allocation_cursor = region_offset
                .checked_add(region.runtime_range().len())
                .ok_or_else(|| {
                    seal_range_error(region.runtime_range(), LoadErrorKind::IntegerOverflow)
                })?;
        }

        let trailing_len = allocation
            .len()
            .checked_sub(allocation_cursor)
            .ok_or_else(|| protection_backend_error(allocation))?;
        append_allocation_range(
            allocation,
            &mut ranges,
            allocation_cursor,
            trailing_len,
            MemoryPermissions::NONE,
        )?;
        validate_logical_cover(allocation, &ranges)?;
        Ok(Self { ranges })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProtectionRecord {
    allocation_offset: AllocationOffset,
    requested_range: TargetRange,
    applied_range: TargetRange,
    permissions: MemoryPermissions,
    level: ProtectionLevel,
}

impl ProtectionRecord {
    #[inline]
    pub const fn allocation_offset(&self) -> AllocationOffset {
        self.allocation_offset
    }

    #[inline]
    pub const fn requested_range(&self) -> TargetRange {
        self.requested_range
    }

    #[inline]
    pub const fn applied_range(&self) -> TargetRange {
        self.applied_range
    }

    #[inline]
    pub const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }

    #[inline]
    pub const fn level(&self) -> ProtectionLevel {
        self.level
    }

    fn record_level(&mut self, level: ProtectionLevel) {
        self.level = level;
    }
}

pub struct ProtectionBatch<'a> {
    records: &'a mut [ProtectionRecord],
}

impl<'a> ProtectionBatch<'a> {
    #[inline]
    pub(crate) const fn new(records: &'a mut [ProtectionRecord]) -> Self {
        Self { records }
    }

    #[inline]
    pub const fn records(&self) -> &[ProtectionRecord] {
        self.records
    }

    pub fn record_level(&mut self, index: usize, level: ProtectionLevel) -> bool {
        let Some(record) = self.records.get_mut(index) else {
            return false;
        };
        record.record_level(level);
        true
    }
}

#[derive(Debug)]
pub struct PreparedProtectionPlan {
    ranges: Vec<ProtectionRecord>,
}

impl PreparedProtectionPlan {
    pub(crate) fn prepare<M: ImageProtectionMemory>(
        transaction: &ImageLoadTransaction<M>,
        logical: &SealPlan,
    ) -> LoadResult<Self> {
        let allocation = *transaction.allocation();
        let prepared = Self::build(&allocation, logical, transaction.protection_capabilities())?;
        transaction.validate_protection_aliases(&prepared)?;
        for range in prepared.ranges() {
            transaction.image_span(range.allocation_offset(), range.applied_range().len())?;
        }
        Ok(prepared)
    }

    pub(crate) fn prepare_for_allocation<M: ImageProtectionMemory + ?Sized>(
        memory: &M,
        allocation: &ImageAllocation,
        logical: &SealPlan,
    ) -> LoadResult<Self> {
        let prepared = Self::build(allocation, logical, memory.protection_capabilities())?;
        memory.validate_protection_aliases(allocation, &prepared)?;
        for range in prepared.ranges() {
            memory.image_span(
                allocation,
                range.allocation_offset(),
                range.applied_range().len(),
            )?;
        }
        Ok(prepared)
    }

    fn build(
        allocation: &ImageAllocation,
        logical: &SealPlan,
        capabilities: ProtectionCapabilities,
    ) -> LoadResult<Self> {
        let granule = capabilities.granule();
        if !granule.is_power_of_two() {
            return Err(protection_backend_error(allocation));
        }
        if logical.ranges().len() > capabilities.max_ranges() {
            return Err(LoadError::new(
                LoadErrorKind::ResourceLimit,
                ErrorContext::Limit {
                    resource: LimitKind::ProtectionRangeCount,
                    actual: logical.ranges().len() as u64,
                    maximum: capabilities.max_ranges() as u64,
                },
            ));
        }

        let mut ranges: Vec<ProtectionRecord> = Vec::new();
        ranges
            .try_reserve_exact(logical.ranges().len())
            .map_err(|_| seal_oom())?;
        let allocation_end = allocation.base().checked_add(allocation.len())?;

        for requested in logical.ranges() {
            let expected_start = allocation
                .base()
                .checked_add(requested.allocation_offset().value())?;
            if expected_start != requested.runtime_range().start() {
                return Err(protection_backend_error(allocation));
            }

            let requested_end = requested.runtime_range().end()?;
            let applied_start = requested.runtime_range().start().align_down(granule)?;
            let applied_end = requested_end.align_up(granule)?;
            if applied_start < allocation.base() || applied_end > allocation_end {
                return Err(protection_backend_error(allocation));
            }
            let prefix = requested
                .runtime_range()
                .start()
                .checked_sub(applied_start)?;
            let applied_offset = requested
                .allocation_offset()
                .value()
                .checked_sub(prefix)
                .ok_or_else(|| protection_backend_error(allocation))?;
            let applied_range =
                TargetRange::new(applied_start, applied_end.checked_sub(applied_start)?);

            if let Some(previous) = ranges.last()
                && previous.applied_range().overlaps(applied_range)
                && previous.permissions() != requested.permissions()
            {
                return Err(seal_range_error(
                    applied_range,
                    LoadErrorKind::PermissionConflict,
                ));
            }

            ranges.push(ProtectionRecord {
                allocation_offset: AllocationOffset::new(applied_offset),
                requested_range: requested.runtime_range(),
                applied_range,
                permissions: requested.permissions(),
                level: ProtectionLevel::LogicalOnly,
            });
        }
        Ok(Self { ranges })
    }

    #[inline]
    pub fn ranges(&self) -> &[ProtectionRecord] {
        &self.ranges
    }

    #[inline]
    pub(crate) fn into_ranges(self) -> Vec<ProtectionRecord> {
        self.ranges
    }
}

#[derive(Clone, Debug)]
pub struct AppliedProtectionSet {
    ranges: Vec<ProtectionRecord>,
}

impl AppliedProtectionSet {
    #[inline]
    pub(crate) const fn new(ranges: Vec<ProtectionRecord>) -> Self {
        Self { ranges }
    }

    #[inline]
    pub fn ranges(&self) -> &[ProtectionRecord] {
        &self.ranges
    }

    pub fn level(&self) -> ProtectionLevel {
        if !self.ranges.is_empty()
            && self
                .ranges
                .iter()
                .all(|range| range.level() == ProtectionLevel::HardwareEnforced)
        {
            ProtectionLevel::HardwareEnforced
        } else {
            ProtectionLevel::LogicalOnly
        }
    }
}

/// The sealed, unpublished payload validated by a commit backend.
///
/// This value carries no allocation authority by itself. In the public API it
/// is always kept private inside `PreparedImage`/`ReadyImageCommit` until the
/// same transaction transfers its unique lease to the committed owner.
#[derive(Clone, Debug)]
pub struct SealedState {
    load_bias: TargetAddress,
    runtime_entry: TargetAddress,
    canonical_entry: TargetAddress,
    cache_sync: CacheSyncOutcome,
    seal_plan: SealPlan,
    protections: AppliedProtectionSet,
}

impl SealedState {
    pub(crate) const fn new(
        load_bias: TargetAddress,
        runtime_entry: TargetAddress,
        canonical_entry: TargetAddress,
        cache_sync: CacheSyncOutcome,
        seal_plan: SealPlan,
        protections: AppliedProtectionSet,
    ) -> Self {
        Self {
            load_bias,
            runtime_entry,
            canonical_entry,
            cache_sync,
            seal_plan,
            protections,
        }
    }

    #[inline]
    pub const fn load_bias(&self) -> TargetAddress {
        self.load_bias
    }

    #[inline]
    pub const fn entry(&self) -> TargetAddress {
        self.runtime_entry
    }

    #[inline]
    pub const fn canonical_entry(&self) -> TargetAddress {
        self.canonical_entry
    }

    #[inline]
    pub const fn cache_sync(&self) -> &CacheSyncOutcome {
        &self.cache_sync
    }

    #[inline]
    pub const fn seal_plan(&self) -> &SealPlan {
        &self.seal_plan
    }

    #[inline]
    pub const fn protections(&self) -> &AppliedProtectionSet {
        &self.protections
    }

    #[inline]
    pub fn protection(&self) -> ProtectionLevel {
        self.protections.level()
    }
}

#[must_use = "dropping a sealed image aborts its allocation"]
pub(crate) struct SealedImage<M: ImageMemory> {
    transaction: ImageLoadTransaction<M>,
    sealed: SealedState,
}

impl<M: ImageMemory> SealedImage<M> {
    pub(crate) fn new(transaction: ImageLoadTransaction<M>, sealed: SealedState) -> Self {
        Self {
            transaction,
            sealed,
        }
    }

    pub(crate) fn into_prepared_parts(self) -> (ImageLoadTransaction<M>, SealedState) {
        (self.transaction, self.sealed)
    }
}

fn validate_region(
    allocation: &ImageAllocation,
    load_bias: TargetAddress,
    segment: &LoadSegmentInfo,
    region: &LoadedRegion,
) -> LoadResult<()> {
    let expected_vaddr = TargetRange::new(segment.vaddr(), segment.memory_size());
    let expected_runtime = TargetRange::new(
        load_bias.checked_add(segment.vaddr().get())?,
        segment.memory_size(),
    );
    let expected_offset = expected_runtime.start().checked_sub(allocation.base())?;
    if region.vaddr_range() != expected_vaddr
        || region.runtime_range() != expected_runtime
        || region.allocation_offset().value() != expected_offset
    {
        return Err(protection_backend_error(allocation));
    }
    region.runtime_range().end()?;
    if segment.permissions().contains(MemoryPermissions::WRITE)
        && segment.permissions().contains(MemoryPermissions::EXECUTE)
    {
        return Err(seal_range_error(
            region.runtime_range(),
            LoadErrorKind::PermissionConflict,
        ));
    }
    Ok(())
}

fn validate_relocation_targets(
    class: ElfClass,
    load_segments: &[LoadSegmentInfo],
    relocations: &[RelocationRecord],
) -> LoadResult<()> {
    let word_len = match class {
        ElfClass::Elf32 => 4,
        ElfClass::Elf64 => 8,
    };
    for relocation in relocations {
        let target = load_segments.iter().find(|segment| {
            TargetRange::new(segment.vaddr(), segment.memory_size())
                .contains_span(relocation.offset(), word_len)
        });
        let kind = match target {
            Some(segment) if segment.permissions().contains(MemoryPermissions::WRITE) => continue,
            Some(_) => LoadErrorKind::PermissionConflict,
            None => LoadErrorKind::OutOfBounds,
        };
        return Err(LoadError::new(
            kind,
            ErrorContext::Relocation {
                offset: relocation.offset(),
                raw_type: relocation.raw_type(),
                symbol_index: relocation.symbol_index(),
            },
        ));
    }
    Ok(())
}

fn validate_relro(load_segments: &[LoadSegmentInfo], relro: Option<TargetRange>) -> LoadResult<()> {
    let Some(relro) = relro else {
        return Ok(());
    };
    let valid = load_segments.iter().any(|segment| {
        segment.permissions().contains(MemoryPermissions::WRITE)
            && TargetRange::new(segment.vaddr(), segment.memory_size())
                .contains_span(relro.start(), relro.len())
    });
    if valid {
        Ok(())
    } else {
        Err(seal_range_error(relro, LoadErrorKind::PermissionConflict))
    }
}

fn append_region_range(
    load_bias: TargetAddress,
    region: &LoadedRegion,
    ranges: &mut Vec<SealRange>,
    vaddr: TargetAddress,
    len: u64,
    permissions: MemoryPermissions,
) -> LoadResult<()> {
    if len == 0 {
        return Ok(());
    }
    let region_delta = vaddr.checked_sub(region.vaddr_range().start())?;
    let allocation_offset = region.allocation_offset().checked_add(region_delta)?;
    let runtime_range = TargetRange::new(load_bias.checked_add(vaddr.get())?, len);
    runtime_range.end()?;
    append_seal_range(ranges, allocation_offset, runtime_range, permissions)
}

fn append_allocation_range(
    allocation: &ImageAllocation,
    ranges: &mut Vec<SealRange>,
    offset: u64,
    len: u64,
    permissions: MemoryPermissions,
) -> LoadResult<()> {
    if len == 0 {
        return Ok(());
    }
    let runtime_range = TargetRange::new(allocation.base().checked_add(offset)?, len);
    runtime_range.end()?;
    append_seal_range(
        ranges,
        AllocationOffset::new(offset),
        runtime_range,
        permissions,
    )
}

fn append_seal_range(
    ranges: &mut Vec<SealRange>,
    allocation_offset: AllocationOffset,
    runtime_range: TargetRange,
    permissions: MemoryPermissions,
) -> LoadResult<()> {
    if let Some(previous) = ranges.last_mut() {
        let previous_offset_end = previous
            .allocation_offset()
            .value()
            .checked_add(previous.runtime_range().len());
        let previous_runtime_end = previous.runtime_range().end()?;
        if previous.permissions() == permissions
            && previous_offset_end == Some(allocation_offset.value())
            && previous_runtime_end == runtime_range.start()
        {
            let merged_len = previous
                .runtime_range()
                .len()
                .checked_add(runtime_range.len())
                .ok_or_else(seal_oom)?;
            previous.runtime_range = TargetRange::new(previous.runtime_range().start(), merged_len);
            return Ok(());
        }
    }
    ranges.push(SealRange {
        allocation_offset,
        runtime_range,
        permissions,
    });
    Ok(())
}

fn validate_logical_cover(allocation: &ImageAllocation, ranges: &[SealRange]) -> LoadResult<()> {
    let mut cursor = 0_u64;
    for range in ranges {
        if range.allocation_offset().value() != cursor {
            return Err(protection_backend_error(allocation));
        }
        cursor = cursor
            .checked_add(range.runtime_range().len())
            .ok_or_else(|| protection_backend_error(allocation))?;
    }
    if cursor == allocation.len() {
        Ok(())
    } else {
        Err(protection_backend_error(allocation))
    }
}

fn seal_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}

fn seal_range_error(range: TargetRange, kind: LoadErrorKind) -> LoadError {
    LoadError::new(
        kind,
        ErrorContext::TargetRange {
            start: range.start(),
            len: range.len(),
            align: 0,
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
