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
use goblin::elf::dynamic::{
    DT_FINI, DT_FINI_ARRAY, DT_FINI_ARRAYSZ, DT_FLAGS, DT_FLAGS_1, DT_GNU_HASH, DT_HASH, DT_INIT,
    DT_INIT_ARRAY, DT_INIT_ARRAYSZ, DT_JMPREL, DT_NEEDED, DT_NULL, DT_PLTREL, DT_PLTRELSZ,
    DT_PREINIT_ARRAY, DT_PREINIT_ARRAYSZ, DT_REL, DT_RELA, DT_RELAENT, DT_RELASZ, DT_RELENT,
    DT_RELSZ, DT_SONAME, DT_STRSZ, DT_STRTAB, DT_SYMENT, DT_SYMTAB,
};

use crate::{
    address::{FileRange, TargetAddress, TargetRange},
    dynamic_linker::{
        symbol_count_from_hash, DependencyName, ImageLifecycleMetadata, ProgramHeaderGeometry,
        RelocationTables, RuntimeImageMetadata, SymbolTable,
    },
    elf::{DynamicSegmentInfo, LoadSegmentInfo},
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::{ElfClass, ElfData, LoadPolicy, LoadRequest, SINGLE_IMAGE_LOAD_POLICY},
    image::{
        decode::{
            DecodedImage, DynamicTags, RelocationAddend, RelocationRecord, RelocationTableKind,
            RelocationTableTags,
        },
        inspect::StackKind,
        read_u32, read_u64,
    },
    memory::{AllocationOffset, ImageLoadTransaction, ImageMemory},
    reader::ElfReader,
};

pub(crate) struct LoadedRegion {
    vaddr_range: TargetRange,
    runtime_range: TargetRange,
    file_range: FileRange,
    allocation_offset: AllocationOffset,
}

impl LoadedRegion {
    #[inline]
    pub const fn new(
        vaddr_range: TargetRange,
        runtime_range: TargetRange,
        file_range: FileRange,
        allocation_offset: AllocationOffset,
    ) -> Self {
        Self {
            vaddr_range,
            runtime_range,
            file_range,
            allocation_offset,
        }
    }

    #[inline]
    pub const fn vaddr_range(&self) -> TargetRange {
        self.vaddr_range
    }

    #[inline]
    pub const fn runtime_range(&self) -> TargetRange {
        self.runtime_range
    }

    #[inline]
    pub const fn file_range(&self) -> FileRange {
        self.file_range
    }

    #[inline]
    pub const fn allocation_offset(&self) -> AllocationOffset {
        self.allocation_offset
    }
}

#[must_use = "dropping a mapped image aborts its allocation"]
pub(crate) struct MappedImage<R: ElfReader, M: ImageMemory> {
    reader: R,
    transaction: ImageLoadTransaction<M>,
    load_bias: TargetAddress,
    request: LoadRequest,
    entry_vaddr: TargetAddress,
    canonical_entry_vaddr: TargetAddress,
    load_segments: Vec<LoadSegmentInfo>,
    regions: Vec<LoadedRegion>,
    dynamic: Option<DynamicSegmentInfo>,
    relro: Option<TargetRange>,
    stack: StackKind,
    interpreter: Option<FileRange>,
    tls: Option<TargetRange>,
    phdr_geometry: ProgramHeaderGeometry,
}

impl<R: ElfReader, M: ImageMemory> MappedImage<R, M> {
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
        relro: Option<TargetRange>,
        stack: StackKind,
        interpreter: Option<FileRange>,
        tls: Option<TargetRange>,
        phdr_geometry: ProgramHeaderGeometry,
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
            relro,
            stack,
            interpreter,
            tls,
            phdr_geometry,
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

    fn locate_file_backed_dynamic(
        &self,
        dynamic: &DynamicSegmentInfo,
    ) -> LoadResult<AllocationOffset> {
        for region in self.regions.iter() {
            if !region
                .vaddr_range()
                .contains_span(dynamic.vaddr(), dynamic.file_range().len())
            {
                continue;
            }
            let offset = dynamic.vaddr().checked_sub(region.vaddr_range().start())?;
            let expected_file_offset = region
                .file_range()
                .offset()
                .checked_add(offset)
                .ok_or_else(|| dynamic_error(DT_NULL, dynamic.file_range().offset()))?;
            // The dynamic bytes must lie wholly within this region's
            // *file-backed* range: a PT_DYNAMIC reaching into BSS is malformed.
            let file_end = offset
                .checked_add(dynamic.file_range().len())
                .filter(|end| *end <= region.file_range().len());
            if file_end.is_none() {
                continue;
            }
            if expected_file_offset == dynamic.file_range().offset() {
                return self.locate_vaddr_at(dynamic.vaddr(), dynamic.file_range().len());
            }
        }
        Err(LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::TargetRange {
                start: dynamic.vaddr(),
                len: dynamic.file_range().len(),
                align: 0,
            },
        ))
    }

    fn decode_dynamic_tags(&self, policy: LoadPolicy) -> LoadResult<DynamicTags> {
        let dynamic = self.dynamic.as_ref().unwrap();
        let entry_size = dynamic_entry_size(self.request.profile().class());

        if dynamic.file_range().is_empty() || dynamic.file_range().len() % entry_size != 0 {
            return Err(dynamic_error(DT_NULL, dynamic.file_range().len()));
        }
        if dynamic.file_range().len() > dynamic.memory_size() {
            return Err(dynamic_error(DT_NULL, dynamic.file_range().len()));
        }
        let offset = self.locate_file_backed_dynamic(dynamic)?;
        self.transaction
            .image_span(offset, dynamic.file_range().len())?;

        let limits = self.request.limits();
        let entry_count = dynamic.file_range().len() / entry_size;
        let mut tags = DynamicTags::default();
        let mut raw = [0; 16];
        let mut terminated = false;
        for index in 0..entry_count {
            limits.check_dynamic_entry_count(index + 1)?;
            let current =
                offset.checked_add(index.checked_mul(entry_size).ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::IntegerOverflow,
                        ErrorContext::DynamicTag {
                            tag: DT_NULL,
                            value: index,
                        },
                    )
                })?)?;
            self.transaction
                .read(current, &mut raw[..entry_size as usize])?;
            let (tag, value) = decode_dynamic_entry(
                &raw[..entry_size as usize],
                self.request.profile().class(),
                self.request.profile().endian(),
            )?;
            if tag == DT_NULL {
                terminated = true;
                break;
            }
            accept_dynamic_tag(&policy, &mut tags, tag, value)?;
        }
        if !terminated {
            return Err(dynamic_error(DT_NULL, dynamic.file_range().len()));
        }
        Ok(tags)
    }

    fn decode_relocation_table(
        &self,
        tags: &RelocationTableTags,
        kind: RelocationTableKind,
        policy: LoadPolicy,
        records: &mut Vec<RelocationRecord>,
    ) -> LoadResult<()> {
        let absent =
            tags.address().is_none() && tags.byte_len().is_none() && tags.entry_size().is_none();
        if absent {
            return Ok(());
        }
        let tag = match kind {
            RelocationTableKind::Rel => DT_REL,
            RelocationTableKind::Rela => DT_RELA,
        };
        let (Some(address), Some(byte_len), Some(entry_size)) =
            (tags.address(), tags.byte_len(), tags.entry_size())
        else {
            return Err(dynamic_error(tag, 0));
        };
        let expected_entry_size = relocation_entry_size(self.request.profile().class(), kind);
        if entry_size != expected_entry_size || byte_len % entry_size != 0 {
            return Err(dynamic_error(tag, entry_size));
        }
        let count = byte_len / entry_size;
        let existing = u64::try_from(records.len()).map_err(|_| dynamic_error(tag, count))?;
        let total = existing
            .checked_add(count)
            .ok_or_else(|| dynamic_error(tag, count))?;
        self.request.limits().check_relocation_count(total)?;
        let count_usize = usize::try_from(count).map_err(|_| dynamic_error(tag, count))?;
        records.try_reserve_exact(count_usize).map_err(|_| {
            LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::DynamicTag { tag, value: count },
            )
        })?;
        let table_vaddr = TargetAddress::new(address);
        if byte_len != 0 {
            let offset = self.locate_vaddr_at(table_vaddr, byte_len)?;
            self.transaction.image_span(offset, byte_len)?;
            let mut raw = [0; 24];
            for index in 0..count {
                let entry_offset = offset.checked_add(index * entry_size)?;
                self.transaction
                    .read(entry_offset, &mut raw[..entry_size as usize])?;
                let record = decode_relocation_entry(
                    &raw[..entry_size as usize],
                    self.request.profile().class(),
                    self.request.profile().endian(),
                    kind,
                )?;
                // Only the multi-image profile understands symbol-bound
                // relocations; the relative engine must fail closed.
                if record.symbol_index() != 0 && !policy.allows_dynamic_symbols() {
                    return Err(unsupported_relocation(record));
                }
                records.push(record);
            }
        }
        Ok(())
    }

    /// Decode the `DT_JMPREL`/`DT_PLTREL` PLT relocation table, if present.
    ///
    /// JMPREL has no per-table `*ENT` tag: its entry geometry is derived from
    /// `DT_PLTREL` (`DT_REL` or `DT_RELA`), which must be present and
    /// self-consistent whenever JMPREL is.
    fn decode_plt_relocations(
        &self,
        tags: &DynamicTags,
        policy: LoadPolicy,
        records: &mut Vec<RelocationRecord>,
    ) -> LoadResult<()> {
        let jmp_absent = tags.jmp_rel().address().is_none()
            && tags.jmp_rel().byte_len().is_none()
            && tags.jmp_rel().entry_size().is_none();
        match (jmp_absent, tags.pltrel()) {
            (true, None) => return Ok(()),
            (true, Some(_)) => return Err(dynamic_error(DT_JMPREL, 0)),
            (false, None) => return Err(dynamic_error(DT_PLTREL, 0)),
            (false, Some(_)) => {}
        }
        let entry_kind = match tags.pltrel() {
            Some(DT_REL) => RelocationTableKind::Rel,
            Some(DT_RELA) => RelocationTableKind::Rela,
            _ => return Err(dynamic_error(DT_PLTREL, tags.pltrel().unwrap_or(0))),
        };
        let entry_size = relocation_entry_size(self.request.profile().class(), entry_kind);
        let synthesized = RelocationTableTags::with_entry_size(tags.jmp_rel(), entry_size);
        self.decode_relocation_table(&synthesized, entry_kind, policy, records)
    }

    pub fn decode(self) -> LoadResult<DecodedImage<R, M>> {
        self.decode_inner(SINGLE_IMAGE_LOAD_POLICY)
    }

    /// Decode with an explicit policy. The public image pipeline stays fixed
    /// to [`SINGLE_IMAGE_LOAD_POLICY`]; the crate-internal `DynamicLinker` passes
    /// [`crate::identity::DYNAMIC_LINK_LOAD_POLICY`] here.
    pub(crate) fn decode_with_policy(self, policy: LoadPolicy) -> LoadResult<DecodedImage<R, M>> {
        self.decode_inner(policy)
    }

    fn decode_inner(mut self, policy: LoadPolicy) -> LoadResult<DecodedImage<R, M>> {
        let mut metadata = RuntimeImageMetadata::empty();
        if self.dynamic.is_some() {
            let tags = self
                .decode_dynamic_tags(policy)
                .map_err(|error| error.at_stage(LoadStage::Decode))?;
            let mut records = Vec::new();
            self.decode_relocation_table(
                tags.rel(),
                RelocationTableKind::Rel,
                policy,
                &mut records,
            )
            .map_err(|error| error.at_stage(LoadStage::Decode))?;
            self.decode_relocation_table(
                tags.rela(),
                RelocationTableKind::Rela,
                policy,
                &mut records,
            )
            .map_err(|error| error.at_stage(LoadStage::Decode))?;
            self.decode_plt_relocations(&tags, policy, &mut records)?;
            let relocations = RelocationTables::new(records);
            let (symbols, needed, soname) = self
                .decode_symbols_and_dependencies(&tags, policy)
                .map_err(|error| error.at_stage(LoadStage::Decode))?;
            let lifecycle = self
                .decode_lifecycle(&tags, policy)
                .map_err(|error| error.at_stage(LoadStage::Decode))?;
            let program_headers = self
                .phdr_geometry
                .resolve(self.load_bias)
                .map_err(|error| error.at_stage(LoadStage::Decode))?;
            metadata = RuntimeImageMetadata::new(
                needed,
                soname,
                symbols,
                relocations,
                lifecycle,
                program_headers,
            );
            self.request
                .limits()
                .check_runtime_metadata_bytes(metadata.metadata_bytes())
                .map_err(|error| error.at_stage(LoadStage::Decode))?;
        }

        Ok(DecodedImage::new(
            self.reader,
            self.transaction,
            self.load_bias,
            self.request,
            self.entry_vaddr,
            self.canonical_entry_vaddr,
            self.load_segments,
            self.regions,
            self.dynamic,
            metadata,
            self.relro,
            self.stack,
            self.interpreter,
            self.tls,
        ))
    }

    /// Decode `.dynstr`, `.dynsym`, and the hash table(s) into an
    /// owned, validated [`SymbolTable`], and resolve the raw `DT_NEEDED`/
    /// `DT_SONAME` offsets into owned [`DependencyName`]s against the same
    /// `.dynstr`. The symbol count is proven from a SysV `DT_HASH` or
    /// GNU `DT_GNU_HASH` table — never from section headers.
    fn decode_symbols_and_dependencies(
        &self,
        tags: &DynamicTags,
        policy: LoadPolicy,
    ) -> LoadResult<(SymbolTable, Vec<DependencyName>, Option<DependencyName>)> {
        if !policy.allows_dynamic_symbols() {
            return Ok((SymbolTable::empty(), Vec::new(), None));
        }
        let class = self.request.profile().class();
        let endian = self.request.profile().endian();
        let thumb = self.request.profile().entry_mode().is_thumb();
        let max_name_len = self.request.limits().max_symbol_name_len();
        let expected_syment: u64 = match class {
            ElfClass::Elf32 => 16,
            ElfClass::Elf64 => 24,
        };

        let any_symbol_tag = tags.symtab().is_some()
            || tags.syment().is_some()
            || tags.strtab().is_some()
            || tags.strsz().is_some()
            || tags.hash().is_some()
            || tags.gnu_hash().is_some()
            || !tags.needed().is_empty()
            || tags.soname().is_some();
        if !any_symbol_tag {
            return Ok((SymbolTable::empty(), Vec::new(), None));
        }

        // `DT_STRTAB`/`DT_STRSZ` and `DT_SYMTAB`/`DT_SYMENT` are paired tags.
        let (strtab, strsz) = match (tags.strtab(), tags.strsz()) {
            (Some(strtab), Some(strsz)) => (strtab, strsz),
            _ => return Err(dynamic_error(DT_STRTAB, 0)),
        };
        let (symtab, syment) = match (tags.symtab(), tags.syment()) {
            (Some(symtab), Some(syment)) => (symtab, syment),
            _ => return Err(dynamic_error(DT_SYMTAB, 0)),
        };
        if syment != expected_syment {
            return Err(dynamic_error(DT_SYMENT, syment));
        }

        self.request.limits().check_string_table_bytes(strsz)?;
        let dynstr = self.read_table_bytes(strtab, strsz, DT_STRTAB)?;

        // Resolve dependency names against the same `.dynstr` before it is
        // moved into the symbol table. `DT_NEEDED` keeps encounter order.
        let needed = self.decode_dependency_names(tags.needed(), &dynstr, DT_NEEDED)?;
        let soname = match tags.soname() {
            Some(offset) => Some(self.decode_dependency_name(offset, &dynstr, DT_SONAME)?),
            None => None,
        };

        let sysv_bytes = match tags.hash() {
            Some(hash_vaddr) => {
                // A SysV table is self-describing: the header carries the
                // bucket/chain counts that bound the whole read.
                let mut header = [0; 8];
                let offset = self.locate_vaddr_at(TargetAddress::new(hash_vaddr), 8)?;
                self.transaction.read(offset, &mut header)?;
                let nbucket = read_u32(&header, 0, endian)?;
                let nchain = read_u32(&header, 4, endian)?;
                let total = 8u64
                    .checked_add(4u64 * (u64::from(nbucket) + u64::from(nchain)))
                    .ok_or_else(|| dynamic_error(DT_HASH, 0))?;
                Some(self.read_table_bytes(hash_vaddr, total, DT_HASH)?)
            }
            None => None,
        };

        let gnu_bytes = match tags.gnu_hash() {
            Some(gnu_vaddr) => Some(
                self.read_gnu_hash_bytes(
                    gnu_vaddr,
                    class,
                    endian,
                    expected_syment,
                    sysv_bytes
                        .as_deref()
                        .map(|bytes| read_u32(bytes, 4, endian))
                        .transpose()?,
                )?,
            ),
            None => None,
        };

        let symbol_count =
            symbol_count_from_hash(class, endian, gnu_bytes.as_deref(), sysv_bytes.as_deref())?;

        let symtab_len = u64::from(symbol_count)
            .checked_mul(syment)
            .ok_or_else(|| dynamic_error(DT_SYMTAB, 0))?;
        // All symbol entries are charged against the total metadata budget
        // *before* parsing, so a malformed table with a huge proven count can
        // never reserve memory past the limit.
        self.request
            .limits()
            .check_runtime_metadata_bytes(symtab_len)?;
        let symtab_bytes = self.read_table_bytes(symtab, symtab_len, DT_SYMTAB)?;

        let symbols = SymbolTable::decode(
            &symtab_bytes,
            dynstr,
            class,
            endian,
            self.load_bias,
            &self.load_segments,
            thumb,
            max_name_len,
            gnu_bytes,
            sysv_bytes,
        )?;
        Ok((symbols, needed, soname))
    }

    /// Decode a list of `DT_NEEDED` offsets into owned, validated
    /// [`DependencyName`]s, bounded by `max_dependency_name_len`.
    fn decode_dependency_names(
        &self,
        offsets: &[u64],
        dynstr: &[u8],
        tag: u64,
    ) -> LoadResult<Vec<DependencyName>> {
        let mut names = Vec::new();
        names.try_reserve_exact(offsets.len()).map_err(|_| {
            LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::DynamicTag {
                    tag,
                    value: offsets.len() as u64,
                },
            )
        })?;
        for &offset in offsets {
            names.push(self.decode_dependency_name(offset, dynstr, tag)?);
        }
        Ok(names)
    }

    /// Decode one `DT_NEEDED`/`DT_SONAME` offset into an owned
    /// [`DependencyName`], bounded by `max_dependency_name_len`.
    fn decode_dependency_name(
        &self,
        offset: u64,
        dynstr: &[u8],
        tag: u64,
    ) -> LoadResult<DependencyName> {
        decode_dependency_name_at(
            offset,
            dynstr,
            tag,
            self.request.limits().max_dependency_name_len(),
        )
    }

    /// Save the lifecycle targets and array ranges without fixing
    /// the array contents into function addresses. The array entry
    /// words are re-read after relocation by the lifecycle plan builder.
    fn decode_lifecycle(
        &self,
        tags: &DynamicTags,
        policy: LoadPolicy,
    ) -> LoadResult<ImageLifecycleMetadata> {
        if !policy.allows_lifecycle() {
            return Ok(ImageLifecycleMetadata::empty());
        }
        let word_size = match self.request.profile().class() {
            ElfClass::Elf32 => 4,
            ElfClass::Elf64 => 8,
        };
        let init = tags.init().map(TargetAddress::new);
        let fini = tags.fini().map(TargetAddress::new);
        let preinit_array = self.array_range(
            tags.preinit_array(),
            tags.preinit_arraysz(),
            word_size,
            DT_PREINIT_ARRAY,
        )?;
        let init_array = self.array_range(
            tags.init_array(),
            tags.init_arraysz(),
            word_size,
            DT_INIT_ARRAY,
        )?;
        let fini_array = self.array_range(
            tags.fini_array(),
            tags.fini_arraysz(),
            word_size,
            DT_FINI_ARRAY,
        )?;
        Ok(ImageLifecycleMetadata::new(
            init,
            fini,
            preinit_array,
            init_array,
            fini_array,
        ))
    }

    /// Pair an init/fini array address with its size into a validated
    /// [`TargetRange`]. Both tags must be present together, the size must be a
    /// whole number of target words, and the range end must not overflow.
    fn array_range(
        &self,
        address: Option<u64>,
        size: Option<u64>,
        word_size: u64,
        tag: u64,
    ) -> LoadResult<Option<TargetRange>> {
        match (address, size) {
            (None, None) => Ok(None),
            (Some(address), Some(size)) => {
                if size % word_size != 0 {
                    return Err(dynamic_error(tag, size));
                }
                let range = TargetRange::new(TargetAddress::new(address), size);
                range.end().map_err(|_| dynamic_error(tag, size))?;
                Ok(Some(range))
            }
            _ => Err(dynamic_error(tag, 0)),
        }
    }

    /// Read `len` bytes at `vaddr` through the owner-bound transaction into an
    /// owned, bounded buffer. A zero-length read yields an empty box without
    /// touching the allocation.
    fn read_table_bytes(&self, vaddr: u64, len: u64, tag: u64) -> LoadResult<Vec<u8>> {
        if len == 0 {
            return Ok(Vec::new());
        }
        let offset = self.locate_vaddr_at(TargetAddress::new(vaddr), len)?;
        self.transaction.image_span(offset, len)?;
        let len_usize = usize::try_from(len).map_err(|_| dynamic_error(tag, len))?;
        let mut buffer = Vec::new();
        buffer.try_reserve_exact(len_usize).map_err(|_| {
            LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::DynamicTag { tag, value: len },
            )
        })?;
        buffer.resize(len_usize, 0);
        self.transaction.read(offset, &mut buffer)?;
        Ok(buffer)
    }

    /// Read exactly the reachable GNU hash extent without relying on section
    /// adjacency. When SysV hash is also present its `nchain` supplies the
    /// symbol count; otherwise the chain beginning at the greatest bucket is
    /// scanned to its bounded terminator.
    fn read_gnu_hash_bytes(
        &self,
        vaddr: u64,
        class: ElfClass,
        endian: ElfData,
        syment: u64,
        known_symbol_count: Option<u32>,
    ) -> LoadResult<Vec<u8>> {
        let header = self.read_table_bytes(vaddr, 16, DT_GNU_HASH)?;
        let nbuckets = read_u32(&header, 0, endian)?;
        let symndx = read_u32(&header, 4, endian)?;
        let maskwords = read_u32(&header, 8, endian)?;
        let shift2 = read_u32(&header, 12, endian)?;
        if nbuckets == 0 || maskwords == 0 || !maskwords.is_power_of_two() || shift2 >= u32::BITS {
            return Err(dynamic_error(DT_GNU_HASH, vaddr));
        }

        let word_size = match class {
            ElfClass::Elf32 => 4_u64,
            ElfClass::Elf64 => 8_u64,
        };
        let head_len = 16_u64
            .checked_add(
                u64::from(maskwords)
                    .checked_mul(word_size)
                    .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?,
            )
            .and_then(|value| value.checked_add(u64::from(nbuckets) * 4))
            .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;

        if let Some(symbol_count) = known_symbol_count {
            let chain_count = symbol_count
                .checked_sub(symndx)
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
            let total = head_len
                .checked_add(u64::from(chain_count) * 4)
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
            self.request.limits().check_runtime_metadata_bytes(total)?;
            return self.read_table_bytes(vaddr, total, DT_GNU_HASH);
        }

        self.request
            .limits()
            .check_runtime_metadata_bytes(head_len)?;
        let head = self.read_table_bytes(vaddr, head_len, DT_GNU_HASH)?;
        let bucket_base = usize::try_from(
            16_u64
                .checked_add(u64::from(maskwords) * word_size)
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?,
        )
        .map_err(|_| dynamic_error(DT_GNU_HASH, vaddr))?;
        let mut greatest_bucket = 0_u32;
        for index in 0..nbuckets as usize {
            let bucket = read_u32(&head, bucket_base + index * 4, endian)?;
            if bucket != 0 && bucket < symndx {
                return Err(dynamic_error(DT_GNU_HASH, u64::from(bucket)));
            }
            greatest_bucket = greatest_bucket.max(bucket);
        }
        if greatest_bucket == 0 {
            return Ok(head);
        }

        let max_symbols = self.request.limits().max_runtime_metadata_bytes() / syment;
        if u64::from(greatest_bucket) >= max_symbols {
            return Err(dynamic_error(DT_GNU_HASH, u64::from(greatest_bucket)));
        }
        let mut chain_index = greatest_bucket - symndx;
        let maximum_chain_count = max_symbols
            .checked_sub(u64::from(symndx))
            .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
        loop {
            if u64::from(chain_index) >= maximum_chain_count {
                return Err(dynamic_error(DT_GNU_HASH, u64::from(chain_index)));
            }
            let word_delta = u64::from(chain_index)
                .checked_mul(4)
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
            let word_vaddr = vaddr
                .checked_add(head_len)
                .and_then(|value| value.checked_add(word_delta))
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
            let word = self.read_table_bytes(word_vaddr, 4, DT_GNU_HASH)?;
            if read_u32(&word, 0, endian)? & 1 != 0 {
                let chain_count = chain_index
                    .checked_add(1)
                    .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
                let total = head_len
                    .checked_add(u64::from(chain_count) * 4)
                    .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
                self.request.limits().check_runtime_metadata_bytes(total)?;
                return self.read_table_bytes(vaddr, total, DT_GNU_HASH);
            }
            chain_index = chain_index
                .checked_add(1)
                .ok_or_else(|| dynamic_error(DT_GNU_HASH, vaddr))?;
        }
    }
}

const fn dynamic_entry_size(class: ElfClass) -> u64 {
    match class {
        ElfClass::Elf32 => 8,
        ElfClass::Elf64 => 16,
    }
}

const fn relocation_entry_size(class: ElfClass, kind: RelocationTableKind) -> u64 {
    match (class, kind) {
        (ElfClass::Elf32, RelocationTableKind::Rel) => 8,
        (ElfClass::Elf32, RelocationTableKind::Rela) => 12,
        (ElfClass::Elf64, RelocationTableKind::Rel) => 16,
        (ElfClass::Elf64, RelocationTableKind::Rela) => 24,
    }
}

pub(crate) fn decode_dynamic_entry(
    bytes: &[u8],
    class: ElfClass,
    endian: ElfData,
) -> LoadResult<(u64, u64)> {
    Ok(match class {
        ElfClass::Elf32 => (
            u64::from(read_u32(bytes, 0, endian)?),
            u64::from(read_u32(bytes, 4, endian)?),
        ),
        ElfClass::Elf64 => (read_u64(bytes, 0, endian)?, read_u64(bytes, 8, endian)?),
    })
}

fn set_once(slot: &mut Option<u64>, tag: u64, value: u64) -> LoadResult<()> {
    if slot.replace(value).is_some() {
        Err(dynamic_error(tag, value))
    } else {
        Ok(())
    }
}

fn decode_relocation_entry(
    bytes: &[u8],
    class: ElfClass,
    endian: ElfData,
    kind: RelocationTableKind,
) -> LoadResult<RelocationRecord> {
    let (offset, info, addend) = match (class, kind) {
        (ElfClass::Elf32, RelocationTableKind::Rel) => (
            u64::from(read_u32(bytes, 0, endian)?),
            u64::from(read_u32(bytes, 4, endian)?),
            RelocationAddend::Implicit,
        ),
        (ElfClass::Elf32, RelocationTableKind::Rela) => (
            u64::from(read_u32(bytes, 0, endian)?),
            u64::from(read_u32(bytes, 4, endian)?),
            RelocationAddend::Explicit(i64::from(read_u32(bytes, 8, endian)? as i32)),
        ),
        (ElfClass::Elf64, RelocationTableKind::Rel) => (
            read_u64(bytes, 0, endian)?,
            read_u64(bytes, 8, endian)?,
            RelocationAddend::Implicit,
        ),
        (ElfClass::Elf64, RelocationTableKind::Rela) => (
            read_u64(bytes, 0, endian)?,
            read_u64(bytes, 8, endian)?,
            RelocationAddend::Explicit(read_u64(bytes, 16, endian)? as i64),
        ),
    };
    let (raw_type, symbol_index) = match class {
        ElfClass::Elf32 => ((info & 0xff) as u32, (info >> 8) as u32),
        ElfClass::Elf64 => (info as u32, (info >> 32) as u32),
    };
    Ok(RelocationRecord::new(
        TargetAddress::new(offset),
        raw_type,
        symbol_index,
        addend,
    ))
}

fn accept_dynamic_tag(
    policy: &LoadPolicy,
    tags: &mut DynamicTags,
    tag: u64,
    value: u64,
) -> LoadResult<()> {
    if !policy.allows_dynamic_tag(tag, value) {
        return Err(unsupported_dynamic(tag, value));
    }
    match tag {
        DT_REL => set_once(tags.rel_mut().address_mut(), tag, value),
        DT_RELSZ => set_once(tags.rel_mut().byte_len_mut(), tag, value),
        DT_RELENT => set_once(tags.rel_mut().entry_size_mut(), tag, value),
        DT_RELA => set_once(tags.rela_mut().address_mut(), tag, value),
        DT_RELASZ => set_once(tags.rela_mut().byte_len_mut(), tag, value),
        DT_RELAENT => set_once(tags.rela_mut().entry_size_mut(), tag, value),
        DT_JMPREL => set_once(tags.jmp_rel_mut().address_mut(), tag, value),
        DT_PLTRELSZ => set_once(tags.jmp_rel_mut().byte_len_mut(), tag, value),
        DT_PLTREL => set_once(tags.pltrel_mut(), tag, value),
        DT_SYMTAB => set_once(tags.symtab_mut(), tag, value),
        DT_SYMENT => set_once(tags.syment_mut(), tag, value),
        DT_STRTAB => set_once(tags.strtab_mut(), tag, value),
        DT_STRSZ => set_once(tags.strsz_mut(), tag, value),
        DT_HASH => set_once(tags.hash_mut(), tag, value),
        DT_GNU_HASH => set_once(tags.gnu_hash_mut(), tag, value),
        DT_NEEDED => tags.push_needed(tag, value),
        DT_SONAME => set_once(tags.soname_mut(), tag, value),
        DT_FLAGS => set_once(tags.flags_mut(), tag, value),
        DT_FLAGS_1 => set_once(tags.flags_1_mut(), tag, value),
        DT_INIT => set_once(tags.init_mut(), tag, value),
        DT_FINI => set_once(tags.fini_mut(), tag, value),
        DT_PREINIT_ARRAY => set_once(tags.preinit_array_mut(), tag, value),
        DT_PREINIT_ARRAYSZ => set_once(tags.preinit_arraysz_mut(), tag, value),
        DT_INIT_ARRAY => set_once(tags.init_array_mut(), tag, value),
        DT_INIT_ARRAYSZ => set_once(tags.init_arraysz_mut(), tag, value),
        DT_FINI_ARRAY => set_once(tags.fini_array_mut(), tag, value),
        DT_FINI_ARRAYSZ => set_once(tags.fini_arraysz_mut(), tag, value),
        _ => Ok(()),
    }
}

pub(crate) fn dynamic_error(tag: u64, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::DynamicTag { tag, value },
    )
}

/// Decode one `DT_NEEDED`/`DT_SONAME` string-table offset into an owned
/// [`DependencyName`], bounded by `max_len`.
///
/// Shared by the map stage and the read-only dependency scanner so both
/// always resolve offsets with the same NUL-scan and length rules.
pub(crate) fn decode_dependency_name_at(
    offset: u64,
    dynstr: &[u8],
    tag: u64,
    max_len: u32,
) -> LoadResult<DependencyName> {
    let start = usize::try_from(offset).map_err(|_| dynamic_error(tag, offset))?;
    let tail = dynstr
        .get(start..)
        .ok_or_else(|| dynamic_error(tag, offset))?;
    let scan = core::cmp::min(max_len as usize + 1, tail.len());
    let nul = tail[..scan]
        .iter()
        .position(|&byte| byte == 0)
        .ok_or_else(|| dynamic_error(tag, offset))?;
    if nul == 0 {
        return Err(dynamic_error(tag, offset));
    }
    DependencyName::from_terminated(&tail[..nul + 1]).map_err(|_| dynamic_error(tag, offset))
}

pub(crate) fn unsupported_dynamic(tag: u64, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::UnsupportedByProfile,
        ErrorContext::DynamicTag { tag, value },
    )
}

fn unsupported_relocation(record: RelocationRecord) -> LoadError {
    LoadError::new(
        LoadErrorKind::UnsupportedByProfile,
        ErrorContext::Relocation {
            offset: record.offset(),
            raw_type: record.raw_type(),
            symbol_index: record.symbol_index(),
        },
    )
}
