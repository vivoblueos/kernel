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

//! Caller-supplied ELF architecture, ABI and admission policies, and resource limits.

use crate::{
    error::{ErrorContext, LimitKind, LoadErrorKind, ProgramHeaderField},
    LoadError, LoadResult,
};
use goblin::elf::{
    header::{
        ELFCLASS32, ELFCLASS64, ELFDATA2LSB, ELFDATA2MSB, EM_AARCH64, EM_RISCV, ET_DYN, ET_EXEC,
    },
    program_header::{
        PF_X, PT_DYNAMIC, PT_GNU_EH_FRAME, PT_GNU_RELRO, PT_GNU_STACK, PT_INTERP, PT_LOAD, PT_NOTE,
        PT_NULL, PT_PHDR, PT_TLS,
    },
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
pub(crate) enum ElfType {
    Dyn,
    Exec,
    Other(u16),
}

impl From<ElfType> for u64 {
    fn from(value: ElfType) -> Self {
        match value {
            ElfType::Dyn => u64::from(ET_DYN),
            ElfType::Exec => u64::from(ET_EXEC),
            ElfType::Other(value) => u64::from(value),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfMachine {
    Riscv,
    Aarch64,
    Other(u16),
}

impl From<ElfMachine> for u64 {
    fn from(value: ElfMachine) -> Self {
        match value {
            ElfMachine::Riscv => u64::from(EM_RISCV),
            ElfMachine::Aarch64 => u64::from(EM_AARCH64),
            ElfMachine::Other(x) => u64::from(x),
        }
    }
}

/// RISC-V `e_flags` bits the loader interprets. The float ABI must be soft for
/// the current RISC-V profiles; the embedded (RVE) register model is unsupported.
const EF_RISCV_FLOAT_ABI_MASK: u32 = 0x0000_0006;
const EF_RISCV_FLOAT_ABI_SOFT: u32 = 0x0000_0000;
const EF_RISCV_RVE: u32 = 0x0000_0008;

/// Processor-specific program header locating RISC-V build attributes.
const PT_RISCV_ATTRIBUTES: u32 = 0x7000_0003;

// Common entries form the prefix. Keep the RISC-V entry last so the default
// policies can share this table without duplicating the common types.
const DEFAULT_PROGRAM_HEADERS: &[u32] = &[
    PT_NULL,
    PT_LOAD,
    PT_DYNAMIC,
    PT_NOTE,
    PT_PHDR,
    PT_GNU_EH_FRAME,
    PT_GNU_RELRO,
    PT_GNU_STACK,
    PT_RISCV_ATTRIBUTES,
];

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

    /// Check the machine-specific flags against the profile constraints.
    #[inline]
    pub const fn accepts(self, flags: u32) -> bool {
        (flags & self.mask) == self.required && (flags & self.forbidden) == 0
    }
}

/// Caller-defined program-header admission policy.
///
/// `new()` replaces the base whitelist. A profile can also retain that list
/// and configure additional types for one load. Accepting metadata does not
/// implement its runtime semantics; matching loading and stack support are
/// still required before executing the image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProgramHeaderPolicy {
    allowed_types: &'static [u32],
    additional_types: &'static [u32],
    executable_stack: bool,
}

impl ProgramHeaderPolicy {
    pub const fn new(allowed_types: &'static [u32], executable_stack: bool) -> Self {
        Self {
            allowed_types,
            additional_types: &[],
            executable_stack,
        }
    }

    /// Base whitelist, excluding the separately configured additional types.
    pub const fn allowed_types(&self) -> &'static [u32] {
        self.allowed_types
    }

    pub const fn additional_types(&self) -> &'static [u32] {
        self.additional_types
    }

    /// Change stack admission while retaining the program-header whitelist.
    pub const fn with_executable_stack(mut self, allowed: bool) -> Self {
        self.executable_stack = allowed;
        self
    }

    fn accepts_type(&self, kind: u32) -> bool {
        self.allowed_types.contains(&kind) || self.additional_types.contains(&kind)
    }

    const fn accepts_stack_flags(&self, flags: u32) -> bool {
        self.executable_stack || flags & PF_X == 0
    }
}

/// Native entry address alignment and the minimum instruction span.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryMode {
    Direct {
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
    pub const fn instruction_alignment(self) -> u8 {
        match self {
            Self::Direct {
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
            } => minimum_instruction_size,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadProfile {
    class: ElfClass,
    endian: ElfData,
    machine: ElfMachine,
    header_flags: HeaderFlagsPolicy,
    entry_mode: EntryMode,
    program_headers: ProgramHeaderPolicy,
}

impl LoadProfile {
    #[inline]
    pub const fn new(
        class: ElfClass,
        endian: ElfData,
        machine: ElfMachine,
        header_flags: HeaderFlagsPolicy,
        entry_mode: EntryMode,
    ) -> Self {
        Self {
            class,
            endian,
            machine,
            header_flags,
            entry_mode,
            program_headers: ProgramHeaderPolicy::new(
                match machine {
                    ElfMachine::Riscv => DEFAULT_PROGRAM_HEADERS,
                    _ => {
                        DEFAULT_PROGRAM_HEADERS
                            .split_at(DEFAULT_PROGRAM_HEADERS.len() - 1)
                            .0
                    }
                },
                false,
            ),
        }
    }

    /// AArch64 little-endian ELF profile with a native aligned entry.
    #[inline]
    pub const fn aarch64() -> Self {
        Self::new(
            ElfClass::Elf64,
            ElfData::Little,
            ElfMachine::Aarch64,
            HeaderFlagsPolicy::new(u32::MAX, 0, 0),
            EntryMode::direct(4, 4),
        )
    }

    /// RISC-V RV32 soft-float profile (RVC permitted, RVE rejected).
    #[inline]
    pub const fn riscv32() -> Self {
        Self::new(
            ElfClass::Elf32,
            ElfData::Little,
            ElfMachine::Riscv,
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
    pub const fn riscv64() -> Self {
        Self::new(
            ElfClass::Elf64,
            ElfData::Little,
            ElfMachine::Riscv,
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
    pub const fn header_flags(&self) -> HeaderFlagsPolicy {
        self.header_flags
    }

    #[inline]
    pub const fn entry_mode(&self) -> EntryMode {
        self.entry_mode
    }

    pub const fn program_header_policy(&self) -> ProgramHeaderPolicy {
        self.program_headers
    }

    /// Replace the default program-header and stack admission policy.
    pub const fn with_program_header_policy(mut self, policy: ProgramHeaderPolicy) -> Self {
        self.program_headers = policy;
        self
    }

    /// Set additional accepted types while retaining the base whitelist and stack policy.
    /// Calling this again replaces the extension list; an empty list clears it.
    pub const fn set_additional_program_headers(&mut self, types: &'static [u32]) {
        self.program_headers.additional_types = types;
    }

    /// Configure additional types when constructing a profile.
    pub const fn with_additional_program_headers(mut self, types: &'static [u32]) -> Self {
        self.set_additional_program_headers(types);
        self
    }

    pub(crate) fn check_program_header(&self, index: u16, kind: u32) -> LoadResult<()> {
        if self.program_headers.accepts_type(kind) {
            return Ok(());
        }
        let field = match kind {
            PT_INTERP => ProgramHeaderField::UnsupportedInterpreter,
            PT_TLS => ProgramHeaderField::UnsupportedTls,
            _ => ProgramHeaderField::Type,
        };
        Err(LoadError::new(
            LoadErrorKind::UnsupportedByProfile,
            ErrorContext::ProgramHeader {
                index,
                field,
                value: u64::from(kind),
            },
        ))
    }

    pub(crate) fn check_stack_flags(&self, index: u16, flags: u32) -> LoadResult<()> {
        if self.program_headers.accepts_stack_flags(flags) {
            return Ok(());
        }
        Err(LoadError::new(
            LoadErrorKind::UnsupportedByProfile,
            ErrorContext::ProgramHeader {
                index,
                field: ProgramHeaderField::ExecutableStack,
                value: u64::from(flags),
            },
        ))
    }
}

/// Per-image bounds checked before reading or retaining header metadata.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadLimits {
    max_file_len: u64,
    max_program_headers: u16,
}

impl LoadLimits {
    pub const DEFAULT: Self = Self::new(64 * 1024 * 1024, 128);

    pub const fn new(max_file_len: u64, max_program_headers: u16) -> Self {
        Self {
            max_file_len,
            max_program_headers,
        }
    }

    pub fn check_file_len(&self, actual: u64) -> LoadResult<()> {
        check_limit(LimitKind::FileLength, actual, self.max_file_len)
    }

    pub fn check_program_header_count(&self, actual: u16) -> LoadResult<()> {
        check_limit(
            LimitKind::ProgramHeaderCount,
            u64::from(actual),
            u64::from(self.max_program_headers),
        )
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
pub(crate) struct LoadRequest {
    profile: LoadProfile,
    limits: LoadLimits,
}

impl LoadRequest {
    pub const fn new(profile: LoadProfile, limits: LoadLimits) -> Self {
        Self { profile, limits }
    }

    pub const fn profile(&self) -> &LoadProfile {
        &self.profile
    }

    pub const fn limits(&self) -> &LoadLimits {
        &self.limits
    }
}
