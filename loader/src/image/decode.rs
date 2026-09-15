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
    address::{FileRange, TargetAddress, TargetRange},
    dynamic_linker::{RuntimeImageMetadata, RuntimeImageState},
    elf::{DynamicSegmentInfo, LoadSegmentInfo},
    error::{ErrorContext, HeaderField, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::LoadRequest,
    image::{inspect::StackKind, map::LoadedRegion, relocate::RelocatedImage},
    memory::{
        AllocationOffset, AllocationRollbackLog, ImageAllocation, ImageLoadTransaction,
        ImageMemory, SessionAllocation,
    },
    reader::ElfReader,
    relocation::{AddendEncoding, ArchRelocator, RelocationOperation, TargetWord, WordWidth},
};

#[derive(Clone, Copy)]
pub(crate) enum RelocationAddend {
    Implicit,
    Explicit(i64),
}

#[derive(Clone, Copy)]
pub(crate) struct RelocationRecord {
    offset: TargetAddress,
    raw_type: u32,
    symbol_index: u32,
    addend: RelocationAddend,
}

impl RelocationRecord {
    #[inline]
    pub const fn new(
        offset: TargetAddress,
        raw_type: u32,
        symbol_index: u32,
        addend: RelocationAddend,
    ) -> Self {
        Self {
            offset,
            raw_type,
            symbol_index,
            addend,
        }
    }

    #[inline]
    pub const fn offset(&self) -> TargetAddress {
        self.offset
    }

    #[inline]
    pub const fn raw_type(&self) -> u32 {
        self.raw_type
    }

    #[inline]
    pub const fn symbol_index(&self) -> u32 {
        self.symbol_index
    }

    #[inline]
    pub const fn addend(&self) -> RelocationAddend {
        self.addend
    }
}

#[must_use = "dropping a decoded image aborts its allocation"]
pub(crate) struct DecodedImage<R: ElfReader, M: ImageMemory> {
    reader: R,
    transaction: ImageLoadTransaction<M>,
    load_bias: TargetAddress,
    request: LoadRequest,
    entry_vaddr: TargetAddress,
    canonical_entry_vaddr: TargetAddress,
    load_segments: Vec<LoadSegmentInfo>,
    regions: Vec<LoadedRegion>,
    dynamic: Option<DynamicSegmentInfo>,
    metadata: RuntimeImageMetadata,
    relro: Option<TargetRange>,
    stack: StackKind,
    interpreter: Option<FileRange>,
    tls: Option<TargetRange>,
}

impl<R: ElfReader, M: ImageMemory> DecodedImage<R, M> {
    #[inline]
    pub fn new(
        reader: R,
        transaction: ImageLoadTransaction<M>,
        load_bias: TargetAddress,
        request: LoadRequest,
        entry_vaddr: TargetAddress,
        canonical_entry_vaddr: TargetAddress,
        load_segments: Vec<LoadSegmentInfo>,
        regions: Vec<LoadedRegion>,
        dynamic: Option<DynamicSegmentInfo>,
        metadata: RuntimeImageMetadata,
        relro: Option<TargetRange>,
        stack: StackKind,
        interpreter: Option<FileRange>,
        tls: Option<TargetRange>,
    ) -> Self {
        Self {
            reader,
            transaction,
            load_bias,
            request,
            entry_vaddr,
            canonical_entry_vaddr,
            load_segments,
            regions,
            dynamic,
            metadata,
            relro,
            stack,
            interpreter,
            tls,
        }
    }

    fn validate_relocator<A: ArchRelocator>(&self, relocator: &A) -> LoadResult<()> {
        let profile = self.request.profile();
        if relocator.machine() == profile.machine() && relocator.class() == profile.class() {
            Ok(())
        } else {
            let (field, value) = if relocator.machine() != profile.machine() {
                (HeaderField::Machine, u64::from(relocator.machine()))
            } else {
                (HeaderField::Class, u64::from(relocator.class()))
            };
            Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::HeaderField { field, value },
            ))
        }
    }

    fn locate_vaddr_at(&self, vaddr: TargetAddress, len: u64) -> LoadResult<AllocationOffset> {
        let region = self
            .regions
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
        let offset = vaddr.checked_sub(region.vaddr_range().start())?;
        region.allocation_offset().checked_add(offset)
    }

    fn preflight_relative<A: ArchRelocator>(
        &self,
        record: RelocationRecord,
        relocator: &A,
        target_word: TargetWord,
    ) -> LoadResult<RelocationOperation> {
        if record.raw_type() != relocator.relative_type() || record.symbol_index() != 0 {
            return Err(relocation_error(
                record,
                LoadErrorKind::UnsupportedByProfile,
            ));
        }
        let width = target_word.width().bytes();
        if record.offset().get() % width != 0 {
            return Err(relocation_error(record, LoadErrorKind::InvalidAlignment));
        }
        let offset = self
            .locate_vaddr_at(record.offset(), width)
            .map_err(|_| relocation_error(record, LoadErrorKind::OutOfBounds))?;
        let writable = self.load_segments.iter().any(|segment| {
            segment
                .permissions()
                .contains(crate::MemoryPermissions::WRITE)
                && TargetRange::new(segment.vaddr(), segment.memory_size())
                    .contains_span(record.offset(), width)
        });
        if !writable {
            return Err(relocation_error(record, LoadErrorKind::PermissionConflict));
        }
        let addend = match (relocator.addend_encoding(), record.addend()) {
            (AddendEncoding::Explicit, RelocationAddend::Explicit(value)) => i128::from(value),
            (AddendEncoding::Implicit, RelocationAddend::Implicit) => match target_word.width() {
                WordWidth::U32 => {
                    i128::from(target_word.read_via(&self.transaction, offset)? as u32 as i32)
                }
                WordWidth::U64 => {
                    i128::from(target_word.read_via(&self.transaction, offset)? as u64 as i64)
                }
            },
            _ => {
                return Err(relocation_error(
                    record,
                    LoadErrorKind::UnsupportedByProfile,
                ))
            }
        };
        let result = i128::from(self.load_bias.get())
            .checked_add(addend)
            .filter(|value| *value >= 0 && *value <= i128::from(target_word.width().maximum()))
            .ok_or_else(|| relocation_error(record, LoadErrorKind::IntegerOverflow))?;
        let value = result as u64;
        let allocation = self.transaction.allocation();
        if !TargetRange::new(allocation.base(), allocation.len())
            .contains_span(TargetAddress::new(value), 1)
        {
            return Err(relocation_error(record, LoadErrorKind::OutOfBounds));
        }
        Ok(RelocationOperation::new(offset, value, record))
    }

    pub fn relocation<A: ArchRelocator>(mut self, relocator: A) -> LoadResult<RelocatedImage<M>> {
        self.validate_relocator(&relocator)
            .map_err(|error| error.at_stage(LoadStage::Relocate))?;
        let target_word = TargetWord::new(
            WordWidth::for_elf_class(self.request.profile().class()),
            self.request.profile().endian(),
        );
        let mut operations = Vec::new();
        let operation_bytes = self
            .metadata
            .relocations()
            .records()
            .len()
            .checked_mul(core::mem::size_of::<RelocationOperation>())
            .and_then(|bytes| u64::try_from(bytes).ok())
            .unwrap_or(u64::MAX);
        self.request
            .limits()
            .check_relocation_operation_bytes(operation_bytes)
            .map_err(|error| error.at_stage(LoadStage::Relocate))?;
        operations
            .try_reserve_exact(self.metadata.relocations().records().len())
            .map_err(|_| {
                LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
                    .at_stage(LoadStage::Relocate)
            })?;

        for record in self.metadata.relocations().records().iter() {
            operations.push(
                self.preflight_relative(*record, &relocator, target_word)
                    .map_err(|error| error.at_stage(LoadStage::Relocate))?,
            );
        }
        operations.sort_unstable_by_key(|operation| operation.offset().value());
        for pair in operations.windows(2) {
            let end = pair[0]
                .offset()
                .checked_add(target_word.width().bytes())
                .map_err(|_| {
                    relocation_error(pair[0].record(), LoadErrorKind::IntegerOverflow)
                        .at_stage(LoadStage::Relocate)
                })?;
            if pair[1].offset() < end {
                return Err(relocation_error(pair[1].record(), LoadErrorKind::BadElf)
                    .at_stage(LoadStage::Relocate));
            }
        }
        for operation in operations {
            target_word
                .write_via(&mut self.transaction, operation.offset(), operation.value())
                .map_err(|error| error.at_stage(LoadStage::Relocate))?;
        }
        Ok(RelocatedImage::new(
            self.transaction,
            self.load_bias,
            self.request,
            self.entry_vaddr,
            self.canonical_entry_vaddr,
            self.load_segments,
            self.regions,
            self.metadata,
            self.relro,
            self.stack,
        ))
    }
}

/// Consume a fully decoded image and absorb its allocation lease into the
/// session rollback log, producing the copyable session descriptor plus the
/// owned runtime state.
///
/// `decoded` owns an `ImageLoadTransaction<&mut M>`: the short reborrow of the
/// session memory ends when the lease is transferred here. On success the
/// unique lease lives only in the rollback log; on failure the transaction's
/// `Drop` aborts the image.
pub(crate) fn absorb_into_session<R, M>(
    decoded: DecodedImage<R, &mut M>,
    rollback: &mut AllocationRollbackLog,
) -> LoadResult<(SessionAllocation, RuntimeImageState)>
where
    R: ElfReader,
    M: ImageMemory + ?Sized,
{
    let DecodedImage {
        transaction,
        load_bias,
        regions,
        load_segments,
        metadata,
        entry_vaddr,
        canonical_entry_vaddr,
        relro,
        stack,
        ..
    } = decoded;
    let session_allocation = transaction.transfer_to(rollback)?;
    let state = RuntimeImageState::new(
        regions,
        load_segments,
        metadata,
        load_bias,
        entry_vaddr,
        canonical_entry_vaddr,
        relro,
        stack,
    );
    Ok((session_allocation, state))
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum RelocationTableKind {
    Rel,
    Rela,
}

#[derive(Default)]
pub(crate) struct RelocationTableTags {
    address: Option<u64>,
    byte_len: Option<u64>,
    entry_size: Option<u64>,
}

impl RelocationTableTags {
    /// Synthesize a JMPREL tag set whose entry size is derived from `DT_PLTREL`
    /// and the ELF class (JMPREL has no per-table `*ENT` tag).
    pub(crate) fn with_entry_size(tags: &RelocationTableTags, entry_size: u64) -> Self {
        Self {
            address: tags.address,
            byte_len: tags.byte_len,
            entry_size: Some(entry_size),
        }
    }

    #[inline]
    pub fn address(&self) -> Option<u64> {
        self.address
    }

    #[inline]
    pub fn byte_len(&self) -> Option<u64> {
        self.byte_len
    }

    #[inline]
    pub fn entry_size(&self) -> Option<u64> {
        self.entry_size
    }

    #[inline]
    pub fn address_mut(&mut self) -> &mut Option<u64> {
        &mut self.address
    }

    #[inline]
    pub fn byte_len_mut(&mut self) -> &mut Option<u64> {
        &mut self.byte_len
    }

    #[inline]
    pub fn entry_size_mut(&mut self) -> &mut Option<u64> {
        &mut self.entry_size
    }
}

#[derive(Default)]
pub(crate) struct DynamicTags {
    rel: RelocationTableTags,
    rela: RelocationTableTags,
    jmp_rel: RelocationTableTags,
    pltrel: Option<u64>,
    symtab: Option<u64>,
    syment: Option<u64>,
    strtab: Option<u64>,
    strsz: Option<u64>,
    hash: Option<u64>,
    gnu_hash: Option<u64>,
    needed: Vec<u64>,
    soname: Option<u64>,
    flags: Option<u64>,
    flags_1: Option<u64>,
    init: Option<u64>,
    fini: Option<u64>,
    preinit_array: Option<u64>,
    preinit_arraysz: Option<u64>,
    init_array: Option<u64>,
    init_arraysz: Option<u64>,
    fini_array: Option<u64>,
    fini_arraysz: Option<u64>,
}

impl DynamicTags {
    #[inline]
    pub fn rel(&self) -> &RelocationTableTags {
        &self.rel
    }

    #[inline]
    pub fn rela(&self) -> &RelocationTableTags {
        &self.rela
    }

    #[inline]
    pub fn rel_mut(&mut self) -> &mut RelocationTableTags {
        &mut self.rel
    }
    #[inline]
    pub fn rela_mut(&mut self) -> &mut RelocationTableTags {
        &mut self.rela
    }

    #[inline]
    pub fn jmp_rel(&self) -> &RelocationTableTags {
        &self.jmp_rel
    }

    #[inline]
    pub fn jmp_rel_mut(&mut self) -> &mut RelocationTableTags {
        &mut self.jmp_rel
    }

    #[inline]
    pub const fn pltrel(&self) -> Option<u64> {
        self.pltrel
    }

    #[inline]
    pub fn pltrel_mut(&mut self) -> &mut Option<u64> {
        &mut self.pltrel
    }

    #[inline]
    pub const fn symtab(&self) -> Option<u64> {
        self.symtab
    }

    #[inline]
    pub const fn syment(&self) -> Option<u64> {
        self.syment
    }

    #[inline]
    pub const fn strtab(&self) -> Option<u64> {
        self.strtab
    }

    #[inline]
    pub const fn strsz(&self) -> Option<u64> {
        self.strsz
    }

    #[inline]
    pub const fn hash(&self) -> Option<u64> {
        self.hash
    }

    #[inline]
    pub const fn gnu_hash(&self) -> Option<u64> {
        self.gnu_hash
    }

    #[inline]
    pub fn symtab_mut(&mut self) -> &mut Option<u64> {
        &mut self.symtab
    }

    #[inline]
    pub fn syment_mut(&mut self) -> &mut Option<u64> {
        &mut self.syment
    }

    #[inline]
    pub fn strtab_mut(&mut self) -> &mut Option<u64> {
        &mut self.strtab
    }

    #[inline]
    pub fn strsz_mut(&mut self) -> &mut Option<u64> {
        &mut self.strsz
    }

    #[inline]
    pub fn hash_mut(&mut self) -> &mut Option<u64> {
        &mut self.hash
    }

    #[inline]
    pub fn gnu_hash_mut(&mut self) -> &mut Option<u64> {
        &mut self.gnu_hash
    }

    #[inline]
    pub fn needed(&self) -> &[u64] {
        &self.needed
    }

    pub fn push_needed(&mut self, tag: u64, value: u64) -> LoadResult<()> {
        self.needed.try_reserve(1).map_err(|_| {
            LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::DynamicTag { tag, value },
            )
        })?;
        self.needed.push(value);
        Ok(())
    }

    #[inline]
    pub const fn soname(&self) -> Option<u64> {
        self.soname
    }

    #[inline]
    pub fn soname_mut(&mut self) -> &mut Option<u64> {
        &mut self.soname
    }

    #[inline]
    pub const fn flags(&self) -> Option<u64> {
        self.flags
    }

    #[inline]
    pub const fn flags_1(&self) -> Option<u64> {
        self.flags_1
    }

    #[inline]
    pub fn flags_mut(&mut self) -> &mut Option<u64> {
        &mut self.flags
    }

    #[inline]
    pub fn flags_1_mut(&mut self) -> &mut Option<u64> {
        &mut self.flags_1
    }

    #[inline]
    pub const fn init(&self) -> Option<u64> {
        self.init
    }

    #[inline]
    pub const fn fini(&self) -> Option<u64> {
        self.fini
    }

    #[inline]
    pub const fn preinit_array(&self) -> Option<u64> {
        self.preinit_array
    }

    #[inline]
    pub const fn preinit_arraysz(&self) -> Option<u64> {
        self.preinit_arraysz
    }

    #[inline]
    pub const fn init_array(&self) -> Option<u64> {
        self.init_array
    }

    #[inline]
    pub const fn init_arraysz(&self) -> Option<u64> {
        self.init_arraysz
    }

    #[inline]
    pub const fn fini_array(&self) -> Option<u64> {
        self.fini_array
    }

    #[inline]
    pub const fn fini_arraysz(&self) -> Option<u64> {
        self.fini_arraysz
    }

    #[inline]
    pub fn init_mut(&mut self) -> &mut Option<u64> {
        &mut self.init
    }

    #[inline]
    pub fn fini_mut(&mut self) -> &mut Option<u64> {
        &mut self.fini
    }

    #[inline]
    pub fn preinit_array_mut(&mut self) -> &mut Option<u64> {
        &mut self.preinit_array
    }

    #[inline]
    pub fn preinit_arraysz_mut(&mut self) -> &mut Option<u64> {
        &mut self.preinit_arraysz
    }

    #[inline]
    pub fn init_array_mut(&mut self) -> &mut Option<u64> {
        &mut self.init_array
    }

    #[inline]
    pub fn init_arraysz_mut(&mut self) -> &mut Option<u64> {
        &mut self.init_arraysz
    }

    #[inline]
    pub fn fini_array_mut(&mut self) -> &mut Option<u64> {
        &mut self.fini_array
    }

    #[inline]
    pub fn fini_arraysz_mut(&mut self) -> &mut Option<u64> {
        &mut self.fini_arraysz
    }
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
