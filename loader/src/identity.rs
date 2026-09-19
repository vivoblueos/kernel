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

use goblin::elf::{
    dynamic::{
        DF_1_NOW, DF_1_PIE, DF_BIND_NOW, DT_BIND_NOW, DT_DEBUG, DT_FINI, DT_FINI_ARRAY,
        DT_FINI_ARRAYSZ, DT_FLAGS, DT_FLAGS_1, DT_GNU_HASH, DT_HASH, DT_INIT, DT_INIT_ARRAY,
        DT_INIT_ARRAYSZ, DT_JMPREL, DT_NEEDED, DT_PLTGOT, DT_PLTREL, DT_PLTRELSZ, DT_PREINIT_ARRAY,
        DT_PREINIT_ARRAYSZ, DT_REL, DT_RELA, DT_RELACOUNT, DT_RELAENT, DT_RELASZ, DT_RELCOUNT,
        DT_RELENT, DT_RELSZ, DT_RPATH, DT_RUNPATH, DT_SONAME, DT_STRSZ, DT_STRTAB, DT_SYMBOLIC,
        DT_SYMENT, DT_SYMTAB, DT_TEXTREL, DT_TLSDESC_GOT, DT_TLSDESC_PLT, DT_VERDEF, DT_VERDEFNUM,
        DT_VERNEED, DT_VERNEEDNUM, DT_VERSYM,
    },
    header::{
        ELFCLASS32, ELFCLASS64, ELFDATA2LSB, ELFDATA2MSB, EM_AARCH64, EM_ARM, EM_RISCV, ET_DYN,
        ET_EXEC,
    },
};

use crate::{
    elf::{DT_RELR, DT_RELRENT, DT_RELRSZ},
    error::{ErrorContext, LimitKind, LoadError, LoadErrorKind, LoadResult},
    memory_mapper::MemoryPermissions,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfClass {
    Elf32,
    Elf64,
}

impl From<ElfClass> for u64 {
    fn from(value: ElfClass) -> Self {
        match value {
            ElfClass::Elf32 => u64::from(ELFCLASS32),
            ElfClass::Elf64 => u64::from(ELFCLASS64),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfData {
    Little,
    Big,
}

impl From<ElfData> for u64 {
    fn from(value: ElfData) -> Self {
        match value {
            ElfData::Little => u64::from(ELFDATA2LSB),
            ElfData::Big => u64::from(ELFDATA2MSB),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfType {
    Dyn,
    Exec,
    Other(u16),
}

impl From<ElfType> for u64 {
    fn from(value: ElfType) -> Self {
        match value {
            ElfType::Dyn => u64::from(ET_DYN),
            ElfType::Exec => u64::from(ET_EXEC),
            ElfType::Other(x) => u64::from(x),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfMachine {
    Riscv,
    Arm,
    Aarch64,
    Other(u16),
}

impl From<ElfMachine> for u64 {
    fn from(value: ElfMachine) -> Self {
        match value {
            ElfMachine::Arm => u64::from(EM_ARM),
            ElfMachine::Riscv => u64::from(EM_RISCV),
            ElfMachine::Aarch64 => u64::from(EM_AARCH64),
            ElfMachine::Other(x) => u64::from(x),
        }
    }
}

/// ARM `e_flags` bits the loader interprets. Only the EABI version and float
/// ABI are gated; the remaining bits are ignored because they do not change
/// how a single BlueOS image is loaded.
const EF_ARM_EABI_MASK: u32 = 0xFF00_0000;
const EF_ARM_EABI_VER5: u32 = 0x0500_0000;
const EF_ARM_ABI_FLOAT_MASK: u32 = 0x0000_0600;
const EF_ARM_ABI_FLOAT_SOFT: u32 = 0x0000_0200;
const EF_ARM_BE8: u32 = 0x0080_0000;

/// RISC-V `e_flags` bits the loader interprets. The float ABI must be soft for
/// the single-image profile; the embedded (RVE) register model is unsupported.
const EF_RISCV_FLOAT_ABI_MASK: u32 = 0x0000_0006;
const EF_RISCV_FLOAT_ABI_SOFT: u32 = 0x0000_0000;
const EF_RISCV_RVE: u32 = 0x0000_0008;

/// Bit-level `e_flags` admission policy for one ELF machine.
///
/// `e_flags` is machine-defined; a policy only ever names the bits its
/// profile understands, so an unknown flag is never interpreted across
/// architectures. A header's flags are accepted when every `required` bit is
/// set, every `forbidden` bit is clear, and the `mask`-selected bits equal
/// `required`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HeaderFlagsPolicy {
    mask: u32,
    required: u32,
    forbidden: u32,
}

impl HeaderFlagsPolicy {
    #[inline]
    pub const fn new(mask: u32, required: u32, forbidden: u32) -> Self {
        Self {
            mask,
            required,
            forbidden,
        }
    }

    /// A policy that accepts any `e_flags`. Reserved for the compatibility
    /// entry point that derives its profile from the artifact rather than a
    /// board ABI; trusted callers must use a named machine profile.
    #[inline]
    pub(crate) const fn permissive() -> Self {
        Self::new(0, 0, 0)
    }

    #[inline]
    pub const fn accepts(self, flags: u32) -> bool {
        (flags & self.mask) == self.required && (flags & self.forbidden) == 0
    }
}

/// How a machine encodes its entry point and the span a load must reserve
/// there so that at least one whole instruction lies inside an executable
/// segment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryMode {
    /// Native instruction set; the entry is the instruction address itself.
    Direct {
        instruction_alignment: u8,
        minimum_instruction_size: u8,
    },
    /// ARM Thumb state; bit 0 of the entry marks Thumb and is cleared before
    /// the address is used for range membership.
    Thumb {
        instruction_alignment: u8,
        minimum_instruction_size: u8,
    },
}

impl EntryMode {
    #[inline]
    pub const fn direct(instruction_alignment: u8, minimum_instruction_size: u8) -> Self {
        Self::Direct {
            instruction_alignment,
            minimum_instruction_size,
        }
    }

    #[inline]
    pub const fn thumb(instruction_alignment: u8, minimum_instruction_size: u8) -> Self {
        Self::Thumb {
            instruction_alignment,
            minimum_instruction_size,
        }
    }

    #[inline]
    pub const fn is_thumb(self) -> bool {
        matches!(self, Self::Thumb { .. })
    }

    #[inline]
    pub const fn instruction_alignment(self) -> u8 {
        match self {
            Self::Direct {
                instruction_alignment,
                ..
            }
            | Self::Thumb {
                instruction_alignment,
                ..
            } => instruction_alignment,
        }
    }

    #[inline]
    pub const fn minimum_instruction_size(self) -> u8 {
        match self {
            Self::Direct {
                minimum_instruction_size,
                ..
            }
            | Self::Thumb {
                minimum_instruction_size,
                ..
            } => minimum_instruction_size,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadProfile {
    class: ElfClass,
    endian: ElfData,
    machine: ElfMachine,
    r#type: ElfType,
    header_flags: HeaderFlagsPolicy,
    entry_mode: EntryMode,
}

impl LoadProfile {
    #[inline]
    pub const fn new(
        class: ElfClass,
        endian: ElfData,
        machine: ElfMachine,
        r#type: ElfType,
        header_flags: HeaderFlagsPolicy,
        entry_mode: EntryMode,
    ) -> Self {
        Self {
            class,
            endian,
            machine,
            r#type,
            header_flags,
            entry_mode,
        }
    }

    /// Cortex-M soft-float Thumb profile (`thumbv7m-none-eabi`): EABI5, soft
    /// float ABI, little-endian Thumb entry with bit 0 set.
    #[inline]
    pub const fn arm_thumb_soft_float(r#type: ElfType) -> Self {
        Self::new(
            ElfClass::Elf32,
            ElfData::Little,
            ElfMachine::Arm,
            r#type,
            HeaderFlagsPolicy::new(
                EF_ARM_EABI_MASK | EF_ARM_ABI_FLOAT_MASK,
                EF_ARM_EABI_VER5 | EF_ARM_ABI_FLOAT_SOFT,
                EF_ARM_BE8,
            ),
            EntryMode::thumb(2, 2),
        )
    }

    /// RISC-V RV32 soft-float profile (RVC permitted, RVE rejected).
    #[inline]
    pub const fn riscv32(r#type: ElfType) -> Self {
        Self::new(
            ElfClass::Elf32,
            ElfData::Little,
            ElfMachine::Riscv,
            r#type,
            HeaderFlagsPolicy::new(
                EF_RISCV_FLOAT_ABI_MASK,
                EF_RISCV_FLOAT_ABI_SOFT,
                EF_RISCV_RVE,
            ),
            EntryMode::direct(2, 2),
        )
    }

    /// RISC-V RV64 soft-float profile (RVC permitted, RVE rejected).
    #[inline]
    pub const fn riscv64(r#type: ElfType) -> Self {
        Self::new(
            ElfClass::Elf64,
            ElfData::Little,
            ElfMachine::Riscv,
            r#type,
            HeaderFlagsPolicy::new(
                EF_RISCV_FLOAT_ABI_MASK,
                EF_RISCV_FLOAT_ABI_SOFT,
                EF_RISCV_RVE,
            ),
            EntryMode::direct(2, 2),
        )
    }

    #[inline]
    pub const fn class(&self) -> ElfClass {
        self.class
    }

    #[inline]
    pub const fn endian(&self) -> ElfData {
        self.endian
    }

    #[inline]
    pub const fn machine(&self) -> ElfMachine {
        self.machine
    }

    #[inline]
    pub const fn r#type(&self) -> ElfType {
        self.r#type
    }

    #[inline]
    pub const fn header_flags(&self) -> HeaderFlagsPolicy {
        self.header_flags
    }

    #[inline]
    pub const fn entry_mode(&self) -> EntryMode {
        self.entry_mode
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadLimits {
    max_file_len: u64,
    max_program_headers: u16,
    max_load_segments: u16,
    max_image_span: u64,
    max_segment_alignment: u64,
    max_dynamic_entries: u64,
    max_relocations: u64,
    max_runtime_metadata_bytes: u64,
    max_relocation_operation_bytes: u64,
    max_string_table_bytes: u64,
    max_symbol_name_len: u32,
    max_dependency_name_len: u32,
}

impl LoadLimits {
    pub const DEFAULT: Self = Self::new(
        64 * 1024 * 1024,
        128,
        32,
        64 * 1024 * 1024,
        1024 * 1024 * 1024,
        1024,
        1024 * 1024,
        64 * 1024 * 1024,
        64 * 1024 * 1024,
        64 * 1024 * 1024,
        256,
        256,
    );

    #[inline]
    pub const fn new(
        max_file_len: u64,
        max_program_headers: u16,
        max_load_segments: u16,
        max_image_span: u64,
        max_segment_alignment: u64,
        max_dynamic_entries: u64,
        max_relocations: u64,
        max_runtime_metadata_bytes: u64,
        max_relocation_operation_bytes: u64,
        max_string_table_bytes: u64,
        max_symbol_name_len: u32,
        max_dependency_name_len: u32,
    ) -> Self {
        Self {
            max_file_len,
            max_program_headers,
            max_load_segments,
            max_image_span,
            max_segment_alignment,
            max_dynamic_entries,
            max_relocations,
            max_runtime_metadata_bytes,
            max_relocation_operation_bytes,
            max_string_table_bytes,
            max_symbol_name_len,
            max_dependency_name_len,
        }
    }

    pub fn check_file_len(&self, actual: u64) -> LoadResult<()> {
        check_limit(LimitKind::FileLength, actual, self.max_file_len)
    }

    pub fn check_program_header_count(&self, actual: u16) -> LoadResult<()> {
        if actual <= self.max_program_headers {
            return Ok(());
        }
        Err(LoadError::new(
            LoadErrorKind::ResourceLimit,
            ErrorContext::Limit {
                resource: LimitKind::ProgramHeaderCount,
                actual: u64::from(actual),
                maximum: u64::from(self.max_program_headers),
            },
        ))
    }

    pub fn check_load_segment_count(&self, actual: usize) -> LoadResult<()> {
        if actual <= usize::from(self.max_load_segments) {
            return Ok(());
        }
        Err(LoadError::new(
            LoadErrorKind::ResourceLimit,
            ErrorContext::Limit {
                resource: LimitKind::LoadSegmentCount,
                actual: actual as u64,
                maximum: u64::from(self.max_load_segments),
            },
        ))
    }

    pub fn check_image_span(&self, actual: u64) -> LoadResult<()> {
        check_limit(LimitKind::ImageSpan, actual, self.max_image_span)
    }

    pub fn check_segment_alignment(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::SegmentAlignment,
            actual,
            self.max_segment_alignment,
        )
    }

    pub fn check_dynamic_entry_count(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::DynamicEntryCount,
            actual,
            self.max_dynamic_entries,
        )
    }

    pub fn check_relocation_count(&self, actual: u64) -> LoadResult<()> {
        check_limit(LimitKind::RelocationCount, actual, self.max_relocations)
    }

    pub fn check_runtime_metadata_bytes(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::RuntimeMetadataBytes,
            actual,
            self.max_runtime_metadata_bytes,
        )
    }

    #[inline]
    pub(crate) const fn max_runtime_metadata_bytes(&self) -> u64 {
        self.max_runtime_metadata_bytes
    }

    pub fn check_relocation_operation_bytes(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::RelocationOperationBytes,
            actual,
            self.max_relocation_operation_bytes,
        )
    }

    pub fn check_string_table_bytes(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::StringTableBytes,
            actual,
            self.max_string_table_bytes,
        )
    }

    #[inline]
    pub const fn max_symbol_name_len(&self) -> u32 {
        self.max_symbol_name_len
    }

    #[inline]
    pub const fn max_dependency_name_len(&self) -> u32 {
        self.max_dependency_name_len
    }
}

fn check_limit(resource: LimitKind, actual: u64, maximum: u64) -> LoadResult<()> {
    if actual <= maximum {
        return Ok(());
    }
    Err(LoadError::new(
        LoadErrorKind::ResourceLimit,
        ErrorContext::Limit {
            resource,
            actual,
            maximum,
        },
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadRequest {
    profile: LoadProfile,
    limits: LoadLimits,
}

impl LoadRequest {
    #[inline]
    pub const fn new(profile: LoadProfile, limits: LoadLimits) -> Self {
        Self { profile, limits }
    }

    #[inline]
    pub const fn profile(&self) -> &LoadProfile {
        &self.profile
    }

    #[inline]
    pub const fn limits(&self) -> &LoadLimits {
        &self.limits
    }
}

/// Session-wide resource budgets for a bounded multi-image link.
///
/// `LoadLimits` keeps governing each individual image; these quotas bound the
/// aggregate session (image count, dependency graph, total metadata, symbol
/// lookup budget). Every `Vec`/map growth must be charged here before it is
/// `try_reserve`d. The `DEFAULT` value is a development ceiling, not a board
/// configuration. The application layer supplies limits from board policy.
/// profile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionLimits {
    per_image: LoadLimits,
    max_images: u32,
    max_dependency_edges: u32,
    max_dependency_depth: u16,
    max_total_image_bytes: u64,
    max_total_runtime_metadata_bytes: u64,
    max_total_relocations: u64,
    max_symbol_lookups: u64,
    max_symbol_name_len: u32,
    max_dependency_name_len: u32,
}

impl SessionLimits {
    pub const DEFAULT: Self = Self::new(
        LoadLimits::DEFAULT,
        64,
        1024,
        32,
        256 * 1024 * 1024,
        256 * 1024 * 1024,
        8 * 1024 * 1024,
        64 * 1024 * 1024,
        256,
        256,
    );

    #[inline]
    pub const fn new(
        per_image: LoadLimits,
        max_images: u32,
        max_dependency_edges: u32,
        max_dependency_depth: u16,
        max_total_image_bytes: u64,
        max_total_runtime_metadata_bytes: u64,
        max_total_relocations: u64,
        max_symbol_lookups: u64,
        max_symbol_name_len: u32,
        max_dependency_name_len: u32,
    ) -> Self {
        Self {
            per_image,
            max_images,
            max_dependency_edges,
            max_dependency_depth,
            max_total_image_bytes,
            max_total_runtime_metadata_bytes,
            max_total_relocations,
            max_symbol_lookups,
            max_symbol_name_len,
            max_dependency_name_len,
        }
    }

    #[inline]
    pub const fn per_image(&self) -> &LoadLimits {
        &self.per_image
    }

    pub fn check_image_count(&self, actual: u32) -> LoadResult<()> {
        check_u32_limit(LimitKind::ImageCount, actual, self.max_images)
    }

    pub fn check_dependency_edge_count(&self, actual: u32) -> LoadResult<()> {
        check_u32_limit(
            LimitKind::DependencyEdgeCount,
            actual,
            self.max_dependency_edges,
        )
    }

    pub fn check_dependency_depth(&self, actual: u16) -> LoadResult<()> {
        check_u32_limit(
            LimitKind::DependencyDepth,
            u32::from(actual),
            u32::from(self.max_dependency_depth),
        )
    }

    pub fn check_total_image_bytes(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::TotalImageBytes,
            actual,
            self.max_total_image_bytes,
        )
    }

    pub fn check_total_runtime_metadata_bytes(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::TotalRuntimeMetadataBytes,
            actual,
            self.max_total_runtime_metadata_bytes,
        )
    }

    pub fn check_total_relocations(&self, actual: u64) -> LoadResult<()> {
        check_limit(
            LimitKind::TotalRelocations,
            actual,
            self.max_total_relocations,
        )
    }

    pub fn check_symbol_lookups(&self, actual: u64) -> LoadResult<()> {
        check_limit(LimitKind::SymbolLookups, actual, self.max_symbol_lookups)
    }

    pub fn check_symbol_name_len(&self, actual: u32) -> LoadResult<()> {
        check_u32_limit(
            LimitKind::SymbolNameLength,
            actual,
            self.max_symbol_name_len,
        )
    }

    pub fn check_dependency_name_len(&self, actual: u32) -> LoadResult<()> {
        check_u32_limit(
            LimitKind::DependencyNameLength,
            actual,
            self.max_dependency_name_len,
        )
    }
}

fn check_u32_limit(resource: LimitKind, actual: u32, maximum: u32) -> LoadResult<()> {
    if actual <= maximum {
        return Ok(());
    }
    Err(LoadError::new(
        LoadErrorKind::ResourceLimit,
        ErrorContext::Limit {
            resource,
            actual: u64::from(actual),
            maximum: u64::from(maximum),
        },
    ))
}

/// Optional ELF capabilities enabled by a load policy.
///
/// This policy only controls optional ELF semantics. Structural checks and
/// safety invariants such as bounds, overflow, overlap and W+X are enforced
/// independently and cannot be disabled here. A capability must not be
/// enabled until its metadata also has a real consumer in the load pipeline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LoadPolicy {
    allow_interpreter: bool,
    allow_tls: bool,
    allow_executable_stack: bool,
    allow_unknown_program_headers: bool,

    allow_execute_only_segments: bool,
    allow_write_only_segments: bool,
    allow_no_access_segments: bool,

    allow_needed: bool,
    allow_plt_relocations: bool,
    require_now_for_plt: bool,
    allow_relr: bool,
    allow_lifecycle: bool,
    allow_search_paths: bool,
    allow_dynamic_symbols: bool,
    allow_symbolic_lookup: bool,
    allow_symbol_versions: bool,
    allow_tls_descriptors: bool,
    allow_unknown_dynamic_tags: bool,
    allowed_dynamic_flags: u64,
    allowed_dynamic_flags_1: u64,
}

impl LoadPolicy {
    #[inline]
    const fn single_image() -> Self {
        Self {
            allow_interpreter: false,
            allow_tls: false,
            allow_executable_stack: false,
            allow_unknown_program_headers: false,

            allow_execute_only_segments: false,
            allow_write_only_segments: false,
            allow_no_access_segments: false,

            allow_needed: false,
            allow_plt_relocations: false,
            require_now_for_plt: false,
            allow_relr: false,
            allow_lifecycle: false,
            allow_search_paths: false,
            allow_dynamic_symbols: false,
            allow_symbolic_lookup: false,
            allow_symbol_versions: false,
            allow_tls_descriptors: false,
            allow_unknown_dynamic_tags: false,
            allowed_dynamic_flags: DF_BIND_NOW,
            allowed_dynamic_flags_1: DF_1_NOW | DF_1_PIE,
        }
    }

    /// Thumbv7 dynamic-link policy. It differs from [`Self::single_image`] only in
    /// the three switches that have a real consumer in the `DynamicLinker`
    /// (`DT_NEEDED`, `DT_JMPREL/DT_PLTREL`, lifecycle arrays); everything else
    /// stays fail-closed so an unsupported feature is never silently accepted.
    #[inline]
    const fn dynamic_link() -> Self {
        Self {
            allow_needed: true,
            allow_plt_relocations: true,
            require_now_for_plt: true,
            allow_lifecycle: true,
            allow_dynamic_symbols: true,
            ..Self::single_image()
        }
    }

    #[inline]
    pub const fn allows_interpreter(&self) -> bool {
        self.allow_interpreter
    }

    #[inline]
    pub const fn allows_tls(&self) -> bool {
        self.allow_tls
    }

    #[inline]
    pub const fn allows_executable_stack(&self) -> bool {
        self.allow_executable_stack
    }

    #[inline]
    pub const fn allows_unknown_program_headers(&self) -> bool {
        self.allow_unknown_program_headers
    }

    #[inline]
    pub const fn allows_dynamic_symbols(&self) -> bool {
        self.allow_dynamic_symbols
    }

    #[inline]
    pub const fn allows_lifecycle(&self) -> bool {
        self.allow_lifecycle
    }

    #[inline]
    pub const fn requires_now_for_plt(&self) -> bool {
        self.require_now_for_plt
    }

    /// Returns whether a non-empty PT_LOAD permission set is supported.
    /// W+X is deliberately absent because it is an unconditional invariant.
    pub fn allows_segment_permissions(&self, permissions: MemoryPermissions) -> bool {
        let read_execute = MemoryPermissions::READ.bitor(MemoryPermissions::EXECUTE);
        let read_write = MemoryPermissions::READ.bitor(MemoryPermissions::WRITE);
        if permissions == MemoryPermissions::READ
            || permissions == read_execute
            || permissions == read_write
        {
            return true;
        }
        if permissions == MemoryPermissions::EXECUTE {
            return self.allow_execute_only_segments;
        }
        if permissions == MemoryPermissions::WRITE {
            return self.allow_write_only_segments;
        }
        if permissions == MemoryPermissions::NONE {
            return self.allow_no_access_segments;
        }
        false
    }

    /// Returns whether the load policy understands and permits a dynamic
    /// tag. Known metadata that is harmless without a consumer is accepted;
    /// tags that introduce linking semantics are controlled explicitly.
    pub const fn allows_dynamic_tag(&self, tag: u64, value: u64) -> bool {
        match tag {
            // Relative relocation tables consumed by the single-image loader.
            DT_REL | DT_RELSZ | DT_RELENT | DT_RELA | DT_RELASZ | DT_RELAENT => true,

            // Text relocations violate the loader's W^X contract in every
            // policy, so they are not represented by an enable switch.
            DT_TEXTREL => false,

            DT_RELR | DT_RELRSZ | DT_RELRENT => self.allow_relr,
            DT_NEEDED => self.allow_needed,
            DT_PLTRELSZ | DT_PLTREL | DT_JMPREL => self.allow_plt_relocations,
            DT_INIT | DT_FINI | DT_INIT_ARRAY | DT_FINI_ARRAY | DT_INIT_ARRAYSZ
            | DT_FINI_ARRAYSZ | DT_PREINIT_ARRAY | DT_PREINIT_ARRAYSZ => self.allow_lifecycle,
            DT_RPATH | DT_RUNPATH => self.allow_search_paths,
            DT_SYMBOLIC => self.allow_symbolic_lookup,
            DT_VERSYM | DT_VERDEF | DT_VERDEFNUM | DT_VERNEED | DT_VERNEEDNUM => {
                self.allow_symbol_versions
            }
            DT_TLSDESC_PLT | DT_TLSDESC_GOT => self.allow_tls_descriptors,

            DT_FLAGS => value & !self.allowed_dynamic_flags == 0,
            DT_FLAGS_1 => value & !self.allowed_dynamic_flags_1 == 0,

            // Recognized metadata that does not by itself request an
            // unsupported runtime operation.
            DT_SONAME | DT_PLTGOT | DT_HASH | DT_STRTAB | DT_SYMTAB | DT_STRSZ | DT_SYMENT
            | DT_DEBUG | DT_BIND_NOW | DT_GNU_HASH | DT_RELACOUNT | DT_RELCOUNT => true,
            _ => self.allow_unknown_dynamic_tags,
        }
    }
}

pub(crate) const SINGLE_IMAGE_LOAD_POLICY: LoadPolicy = LoadPolicy::single_image();
pub(crate) const DYNAMIC_LINK_LOAD_POLICY: LoadPolicy = LoadPolicy::dynamic_link();
