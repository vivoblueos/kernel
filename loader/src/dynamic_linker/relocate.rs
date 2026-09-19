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

//! Session-wide relocation engine.
//!
//! Every admitted image contributes its decoded [`RelocationRecord`]s; this
//! module resolves them against the frozen [`ScopeSet`], performs the full
//! session-wide preflight, and applies the results in the fixed
//! three-pass order (relative → data/global → PLT). All writes go through the
//! session rollback log so a backend failure aborts the whole link.

use alloc::vec::Vec;

use crate::{
    address::{TargetAddress, TargetRange},
    dynamic_linker::{
        session::SessionUsage, ImageId, ResolvedSymbol, RuntimeImageMetadata, ScopeSet,
        SymbolBinding, SymbolDefinition, SymbolRegionKind, SymbolTable, SymbolVisibility,
    },
    elf::LoadSegmentInfo,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::{ElfMachine, LoadProfile, SessionLimits},
    image::{LoadedRegion, RelocationAddend, RelocationRecord},
    memory::{
        AllocationOffset, AllocationRollbackLog, ImageAllocation, ImageMemory, SessionAllocation,
    },
    relocation::{AddendEncoding, ArchRelocator, RelocationKind, TargetWord, WordWidth},
    MemoryPermissions,
};

/// The set of relocation kinds a profile's engine understands.
///
/// The `ARM32` set contains the four relocation kinds supported by eager
/// binding. Other profiles expose an empty set until they gain an engine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RelocationTypeSet(u8);

impl RelocationTypeSet {
    const RELATIVE: u8 = 1 << 0;
    const ABSOLUTE: u8 = 1 << 1;
    const GLOBAL_DATA: u8 = 1 << 2;
    const JUMP_SLOT: u8 = 1 << 3;

    const fn bit(kind: RelocationKind) -> u8 {
        match kind {
            RelocationKind::Relative => Self::RELATIVE,
            RelocationKind::Absolute => Self::ABSOLUTE,
            RelocationKind::GlobalData => Self::GLOBAL_DATA,
            RelocationKind::JumpSlot => Self::JUMP_SLOT,
        }
    }

    const fn empty() -> Self {
        Self(0)
    }

    const fn arm_now() -> Self {
        Self(Self::RELATIVE | Self::ABSOLUTE | Self::GLOBAL_DATA | Self::JUMP_SLOT)
    }

    #[inline]
    const fn contains(self, kind: RelocationKind) -> bool {
        self.0 & Self::bit(kind) != 0
    }
}

/// Session-wide relocation acceptance rules.
///
/// Constructed from the profile and
/// [`DYNAMIC_LINK_LOAD_POLICY`](crate::identity::DYNAMIC_LINK_LOAD_POLICY);
/// callers can never supply an arbitrary type set.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RelocationPolicy {
    allowed_types: RelocationTypeSet,
    allow_undefined_weak_data: bool,
    allow_undefined_weak_control_flow: bool,
    require_control_flow_target_x: bool,
    require_target_owner_writable: bool,
}

impl RelocationPolicy {
    /// The policy for a profile. Only ARM32 has a NOW engine so far; every
    /// other machine is fail-closed.
    pub(crate) const fn for_profile(profile: &LoadProfile) -> Self {
        match profile.machine() {
            ElfMachine::Arm => Self::arm_now(),
            _ => Self::fail_closed(),
        }
    }

    const fn fail_closed() -> Self {
        Self {
            allowed_types: RelocationTypeSet::empty(),
            allow_undefined_weak_data: false,
            allow_undefined_weak_control_flow: false,
            require_control_flow_target_x: true,
            require_target_owner_writable: true,
        }
    }

    const fn arm_now() -> Self {
        Self {
            allowed_types: RelocationTypeSet::arm_now(),
            // Undefined weak data binds to 0; undefined weak control flow does
            // not; unsupported binding combinations are rejected.
            allow_undefined_weak_data: true,
            allow_undefined_weak_control_flow: false,
            require_control_flow_target_x: true,
            require_target_owner_writable: true,
        }
    }
}

/// Provenance of a resolved relocation value.
#[derive(Clone, Copy, Debug)]
pub(crate) enum RelocationSource {
    /// `B + A`: the load bias plus addend, no symbol.
    Relative,
    /// A resolved symbol from the frozen scopes.
    Symbol(ResolvedSymbol),
    /// An undefined weak reference, resolved to zero.
    UndefinedWeak,
}

/// One fully preflighted session relocation, ready to apply.
#[derive(Clone)]
pub(crate) struct SessionRelocation {
    owner: ImageId,
    target_offset: AllocationOffset,
    kind: RelocationKind,
    value: u64,
    source: RelocationSource,
    record: RelocationRecord,
}

impl SessionRelocation {
    #[inline]
    pub(crate) const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub(crate) const fn kind(&self) -> RelocationKind {
        self.kind
    }

    #[inline]
    pub(crate) const fn source(&self) -> &RelocationSource {
        &self.source
    }

    /// The decoded relocation record (symbol index and image-relative
    /// target offset) this operation was preflighted from.
    #[inline]
    pub(crate) const fn record(&self) -> &RelocationRecord {
        &self.record
    }
}

/// Per-image inputs to the session relocation engine, borrowed from the
/// session's `RuntimeImageState`.
pub(crate) struct RelocationImage<'a> {
    image_id: ImageId,
    allocation: SessionAllocation,
    regions: &'a [LoadedRegion],
    load_segments: &'a [LoadSegmentInfo],
    metadata: &'a RuntimeImageMetadata,
    load_bias: TargetAddress,
}

impl<'a> RelocationImage<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        image_id: ImageId,
        allocation: SessionAllocation,
        regions: &'a [LoadedRegion],
        load_segments: &'a [LoadSegmentInfo],
        metadata: &'a RuntimeImageMetadata,
        load_bias: TargetAddress,
    ) -> Self {
        Self {
            image_id,
            allocation,
            regions,
            load_segments,
            metadata,
            load_bias,
        }
    }

    #[inline]
    pub(crate) const fn allocation(&self) -> SessionAllocation {
        self.allocation
    }
}

/// One provider-visible region of an image, used to validate a control-flow or
/// data target against its owner's mapped ranges.
///
/// For a loaded image this pairs each `LoadSegmentInfo` permission with the
/// runtime range of the region mapped from it; for an imported Ready image it
/// is derived directly from a [`crate::dynamic_linker::PublishedRegion`]. The
/// relocation engine indexes these by [`ImageId`] over every admitted image —
/// loaded and imported — so a symbol resolved into an imported provider is
/// range-checked against the same facts a fresh load would have produced.
#[derive(Clone, Copy)]
pub(crate) struct ProviderRegion {
    permissions: MemoryPermissions,
    runtime_range: TargetRange,
}

impl ProviderRegion {
    #[inline]
    pub(crate) const fn new(permissions: MemoryPermissions, runtime_range: TargetRange) -> Self {
        Self {
            permissions,
            runtime_range,
        }
    }

    #[inline]
    pub(crate) const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }

    #[inline]
    pub(crate) const fn runtime_range(&self) -> TargetRange {
        self.runtime_range
    }
}

/// Run the complete session-wide relocation: preflight every record into an
/// ordered operation list, then apply in the fixed three-pass order.
///
/// Returns the ordered operations (already applied) so the caller can retain
/// each scope decision before sealing.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run<A, M>(
    arch: &A,
    symbols: &[&SymbolTable],
    images: &[Option<RelocationImage<'_>>],
    provider_regions: &[Vec<ProviderRegion>],
    scopes: &ScopeSet,
    profile: &LoadProfile,
    policy: &RelocationPolicy,
    limits: &SessionLimits,
    usage: &mut SessionUsage,
    memory: &mut M,
    log: &mut AllocationRollbackLog,
) -> LoadResult<Vec<SessionRelocation>>
where
    A: ArchRelocator + ?Sized,
    M: ImageMemory + ?Sized,
{
    let operations = preflight(
        arch,
        symbols,
        images,
        provider_regions,
        scopes,
        profile,
        policy,
        limits,
        usage,
        &*memory,
    )?;
    apply(&operations, images, profile, memory, log)?;
    Ok(operations)
}

/// Preflight: resolve every record into a validated, ordered operation list
/// without writing. Implicit REL addends are read here so no write happens
/// before the full session has been proven.
#[allow(clippy::too_many_arguments)]
fn preflight<A, M>(
    arch: &A,
    symbols: &[&SymbolTable],
    images: &[Option<RelocationImage<'_>>],
    provider_regions: &[Vec<ProviderRegion>],
    scopes: &ScopeSet,
    profile: &LoadProfile,
    policy: &RelocationPolicy,
    limits: &SessionLimits,
    usage: &mut SessionUsage,
    memory: &M,
) -> LoadResult<Vec<SessionRelocation>>
where
    A: ArchRelocator + ?Sized,
    M: ImageMemory + ?Sized,
{
    let width = WordWidth::for_elf_class(profile.class());
    let target_word = TargetWord::new(width, profile.endian());
    let thumb = profile.entry_mode().is_thumb();

    let total = images.iter().flatten().try_fold(0_u64, |total, image| {
        total
            .checked_add(image.metadata.relocations().len() as u64)
            .ok_or_else(relocation_oom)
    })?;
    limits
        .check_total_relocations(total)
        .map_err(|error| error.at_stage(LoadStage::LinkRelocate))?;
    let operation_count = usize::try_from(total).map_err(|_| relocation_oom())?;
    let mut operations = Vec::new();
    operations
        .try_reserve_exact(operation_count)
        .map_err(|_| relocation_oom())?;
    for image in images.iter().flatten() {
        for record in image.metadata.relocations().records().iter() {
            let operation = preflight_one(
                arch,
                symbols,
                scopes,
                provider_regions,
                policy,
                limits,
                target_word,
                thumb,
                image,
                *record,
                usage,
                memory,
            )
            .map_err(|error| error.at_stage(LoadStage::LinkRelocate))?;
            operations.push(operation);
        }
    }

    operations.sort_unstable_by_key(|op| (op.owner.get(), op.target_offset.value()));
    reject_overlapping_targets(&operations, width)?;

    Ok(operations)
}

#[allow(clippy::too_many_arguments)]
fn preflight_one<A, M>(
    arch: &A,
    symbols: &[&SymbolTable],
    scopes: &ScopeSet,
    provider_regions: &[Vec<ProviderRegion>],
    policy: &RelocationPolicy,
    limits: &SessionLimits,
    target_word: TargetWord,
    thumb: bool,
    image: &RelocationImage<'_>,
    record: RelocationRecord,
    usage: &mut SessionUsage,
    memory: &M,
) -> LoadResult<SessionRelocation>
where
    A: ArchRelocator + ?Sized,
    M: ImageMemory + ?Sized,
{
    // the raw type must be in the profile whitelist.
    let kind = arch
        .classify_relocation(record.raw_type())
        .filter(|kind| policy.allowed_types.contains(*kind))
        .ok_or_else(|| relocation_error(record, LoadErrorKind::UnsupportedByProfile))?;

    // target alignment.
    let width = target_word.width();
    if record.offset().get() % width.bytes() != 0 {
        return Err(relocation_error(record, LoadErrorKind::InvalidAlignment));
    }

    // the complete target word must be owner-bound and writable.
    let allocation = image.allocation().allocation();
    let offset = locate_region_offset(image.regions, record.offset(), width.bytes())
        .map_err(|_| relocation_error(record, LoadErrorKind::OutOfBounds))?;
    if policy.require_target_owner_writable
        && !segment_is_writable(image.load_segments, record.offset(), width.bytes())
    {
        return Err(relocation_error(record, LoadErrorKind::PermissionConflict));
    }
    image
        .load_bias
        .checked_add(record.offset().get())
        .map_err(|_| relocation_error(record, LoadErrorKind::IntegerOverflow))?;

    // Resolve the addend and the symbol value, then fold into the final word.
    let addend = resolve_addend(arch, target_word, record, offset, allocation, memory)?;
    let source = resolve_source(
        arch,
        symbols,
        scopes,
        provider_regions,
        policy,
        limits,
        thumb,
        image.image_id,
        record,
        kind,
        usage,
    )?;
    let value = fold_value(kind, image.load_bias, &source, addend, width, record)?;
    if kind == RelocationKind::Relative
        && !TargetRange::new(allocation.base(), allocation.len())
            .contains_span(TargetAddress::new(value), 1)
    {
        return Err(relocation_error(record, LoadErrorKind::OutOfBounds));
    }

    Ok(SessionRelocation {
        owner: image.image_id,
        target_offset: offset,
        kind,
        value,
        source,
        record,
    })
}

/// Resolve the addend: an explicit RELA addend is used directly; an implicit
/// REL addend is read from the target word and sign-extended per the word
/// width.
fn resolve_addend<A, M>(
    arch: &A,
    target_word: TargetWord,
    record: RelocationRecord,
    offset: AllocationOffset,
    allocation: ImageAllocation,
    memory: &M,
) -> LoadResult<i128>
where
    A: ArchRelocator + ?Sized,
    M: ImageMemory + ?Sized,
{
    match (arch.addend_encoding(), record.addend()) {
        (AddendEncoding::Implicit, RelocationAddend::Implicit) => {
            let word = target_word.read(memory, &allocation, offset)?;
            Ok(implicit_addend(word, target_word.width()))
        }
        (AddendEncoding::Explicit, RelocationAddend::Explicit(value)) => Ok(i128::from(value)),
        _ => Err(relocation_error(
            record,
            LoadErrorKind::UnsupportedByProfile,
        )),
    }
}

/// Sign-extend a target word into a signed addend, centralized so the ARM
/// psABI's signedness rules never leak `as` casts into the engine.
fn implicit_addend(word: u64, width: WordWidth) -> i128 {
    match width {
        WordWidth::U32 => i128::from(word as u32 as i32),
        WordWidth::U64 => i128::from(word as u64 as i64),
    }
}

/// Resolve the symbol a relocation references into its runtime value and
/// provenance ( + ).
#[allow(clippy::too_many_arguments)]
fn resolve_source<A>(
    _arch: &A,
    symbols: &[&SymbolTable],
    scopes: &ScopeSet,
    provider_regions: &[Vec<ProviderRegion>],
    policy: &RelocationPolicy,
    limits: &SessionLimits,
    thumb: bool,
    owner: ImageId,
    record: RelocationRecord,
    kind: RelocationKind,
    usage: &mut SessionUsage,
) -> LoadResult<RelocationSource>
where
    A: ArchRelocator + ?Sized,
{
    // RELATIVE has no symbol; its value is B + A.
    if kind == RelocationKind::Relative {
        if record.symbol_index() != 0 {
            return Err(relocation_error(record, LoadErrorKind::BadElf));
        }
        return Ok(RelocationSource::Relative);
    }

    let table = symbols
        .get(owner.get() as usize)
        .ok_or_else(|| relocation_error(record, LoadErrorKind::BadElf))?;
    // the symbol index must be within the proven dynsym count.
    let entry = table
        .entry(record.symbol_index())
        .ok_or_else(|| relocation_error(record, LoadErrorKind::BadElf))?;

    let resolved = match (entry.binding(), entry.visibility(), entry.definition()) {
        // Local references never enter an external scope.
        (SymbolBinding::Local, _, SymbolDefinition::Defined) => {
            scopes.resolve_index(symbols, owner, record.symbol_index())
        }
        (SymbolBinding::Local, _, SymbolDefinition::Undefined) => {
            return Err(relocation_error(record, LoadErrorKind::BadElf));
        }

        // Non-default visibility cannot be satisfied by another image. A
        // defined hidden/internal/protected reference binds to this exact
        // symbol index; an undefined one is malformed.
        (
            SymbolBinding::Global | SymbolBinding::Weak,
            SymbolVisibility::Hidden | SymbolVisibility::Internal | SymbolVisibility::Protected,
            SymbolDefinition::Defined,
        ) => scopes.resolve_index(symbols, owner, record.symbol_index()),
        (
            SymbolBinding::Global | SymbolBinding::Weak,
            SymbolVisibility::Hidden | SymbolVisibility::Internal | SymbolVisibility::Protected,
            SymbolDefinition::Undefined,
        ) => return Err(relocation_error(record, LoadErrorKind::BadElf)),

        // Default-visible definitions are preemptible. Search the requester's
        // frozen scope even when the referenced entry is defined locally.
        (SymbolBinding::Global | SymbolBinding::Weak, SymbolVisibility::Default, _) => {
            let name = table.name(entry);
            limits.check_symbol_name_len(name.len() as u32)?;
            scopes.resolve_name(symbols, owner, name, limits, usage)?
        }
    };

    match resolved {
        Some(symbol) => {
            validate_symbol_kind(kind, thumb, &symbol, provider_regions, policy, record)?;
            Ok(RelocationSource::Symbol(symbol))
        }
        None => {
            // Undefined strong fails; undefined weak binds to zero under the
            // data and control-flow relocation rules.
            if entry.binding() != SymbolBinding::Weak {
                return Err(relocation_error(record, LoadErrorKind::BadElf));
            }
            let is_control_flow = kind == RelocationKind::JumpSlot;
            let allowed = if is_control_flow {
                policy.allow_undefined_weak_control_flow
            } else {
                policy.allow_undefined_weak_data
            };
            if !allowed {
                return Err(relocation_error(record, LoadErrorKind::BadElf));
            }
            Ok(RelocationSource::UndefinedWeak)
        }
    }
}

/// Validate that a resolved symbol is compatible with the relocation kind:
/// control-flow must target an executable region with a correct Thumb bit.
fn validate_symbol_kind(
    kind: RelocationKind,
    thumb: bool,
    symbol: &ResolvedSymbol,
    provider_regions: &[Vec<ProviderRegion>],
    policy: &RelocationPolicy,
    record: RelocationRecord,
) -> LoadResult<()> {
    if kind == RelocationKind::JumpSlot && symbol.region() != SymbolRegionKind::Executable {
        return Err(relocation_error(record, LoadErrorKind::BadElf));
    }
    if thumb && symbol.region() == SymbolRegionKind::Executable && symbol.address().get() & 1 == 0 {
        return Err(relocation_error(record, LoadErrorKind::BadElf));
    }
    if kind == RelocationKind::JumpSlot {
        if symbol.is_absolute() {
            return Err(relocation_error(
                record,
                LoadErrorKind::UnsupportedByProfile,
            ));
        }
        if policy.require_control_flow_target_x {
            let provider = provider_regions
                .get(symbol.owner().get() as usize)
                .ok_or_else(|| relocation_error(record, LoadErrorKind::BadElf))?;
            let span = core::cmp::max(symbol.size(), 1);
            let executable = provider.iter().any(|region| {
                region.permissions().contains(MemoryPermissions::EXECUTE)
                    && region
                        .runtime_range()
                        .contains_span(symbol.canonical(), span)
            });
            if !executable {
                return Err(relocation_error(record, LoadErrorKind::PermissionConflict));
            }
        }
    }
    Ok(())
}

/// Fold a resolved symbol/addend into the final target word with checked
/// arithmetic and result-range validation.
fn fold_value(
    kind: RelocationKind,
    load_bias: TargetAddress,
    source: &RelocationSource,
    addend: i128,
    width: WordWidth,
    record: RelocationRecord,
) -> LoadResult<u64> {
    let base = match (kind, source) {
        (RelocationKind::Relative, _) => i128::from(load_bias.get()),
        (_, RelocationSource::Symbol(symbol)) => i128::from(symbol.address().get()),
        (_, RelocationSource::UndefinedWeak) => 0,
        (_, RelocationSource::Relative) => {
            return Err(relocation_error(record, LoadErrorKind::BadElf));
        }
    };
    let (base, addend) = match kind {
        RelocationKind::Relative | RelocationKind::Absolute => (base, addend),
        RelocationKind::GlobalData | RelocationKind::JumpSlot => (base, 0),
    };
    let result = base
        .checked_add(addend)
        .ok_or_else(|| relocation_error(record, LoadErrorKind::IntegerOverflow))?;
    let maximum = i128::from(width.maximum());
    if result < 0 || result > maximum {
        return Err(relocation_error(record, LoadErrorKind::IntegerOverflow));
    }
    Ok(result as u64)
}

/// reject duplicate or overlapping target words.
fn reject_overlapping_targets(
    operations: &[SessionRelocation],
    width: WordWidth,
) -> LoadResult<()> {
    for pair in operations.windows(2) {
        if pair[0].owner != pair[1].owner {
            continue;
        }
        let end = pair[0]
            .target_offset
            .checked_add(width.bytes())
            .map_err(|_| LoadError::new(LoadErrorKind::IntegerOverflow, ErrorContext::None))?;
        if pair[1].target_offset < end {
            return Err(relocation_error(pair[1].record, LoadErrorKind::BadElf));
        }
    }
    Ok(())
}

/// Apply the ordered operations in the fixed three-pass order: relative, then
/// data/global, then PLT/JUMP_SLOT.
fn apply<M: ImageMemory + ?Sized>(
    operations: &[SessionRelocation],
    images: &[Option<RelocationImage<'_>>],
    profile: &LoadProfile,
    memory: &mut M,
    log: &mut AllocationRollbackLog,
) -> LoadResult<()> {
    let target_word = TargetWord::new(WordWidth::for_elf_class(profile.class()), profile.endian());
    for pass in [
        RelocationKind::Relative,
        RelocationKind::Absolute,
        RelocationKind::GlobalData,
        RelocationKind::JumpSlot,
    ] {
        for operation in operations.iter().filter(|op| op.kind == pass) {
            let image = images[operation.owner.get() as usize]
                .as_ref()
                .ok_or_else(|| relocation_error(operation.record, LoadErrorKind::BadElf))?;
            log.mark_bytes_modified(image.allocation())
                .map_err(|error| error.at_stage(LoadStage::LinkRelocate))?;
            let allocation = image.allocation().allocation();
            target_word
                .write(
                    memory,
                    &allocation,
                    operation.target_offset,
                    operation.value,
                )
                .map_err(|error| error.at_stage(LoadStage::LinkRelocate))?;
        }
    }
    Ok(())
}

pub(crate) fn locate_region_offset(
    regions: &[LoadedRegion],
    vaddr: TargetAddress,
    len: u64,
) -> LoadResult<AllocationOffset> {
    let region = regions
        .iter()
        .find(|region| region.vaddr_range().contains_span(vaddr, len))
        .ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::OutOfBounds,
                ErrorContext::TargetRange {
                    start: vaddr,
                    len,
                    align: 0,
                },
            )
        })?;
    let delta = vaddr.checked_sub(region.vaddr_range().start())?;
    region.allocation_offset().checked_add(delta)
}

fn segment_is_writable(segments: &[LoadSegmentInfo], vaddr: TargetAddress, len: u64) -> bool {
    segments.iter().any(|segment| {
        segment.permissions().contains(MemoryPermissions::WRITE)
            && crate::address::TargetRange::new(segment.vaddr(), segment.memory_size())
                .contains_span(vaddr, len)
    })
}

fn relocation_error(record: RelocationRecord, kind: LoadErrorKind) -> LoadError {
    LoadError::new(
        kind,
        ErrorContext::Relocation {
            offset: record.offset(),
            raw_type: record.raw_type(),
            symbol_index: record.symbol_index(),
        },
    )
}

fn relocation_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}
