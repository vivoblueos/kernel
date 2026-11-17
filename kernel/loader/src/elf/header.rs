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

use super::{
    read_u16, read_u32, read_u64, ELF32_HEADER_SIZE, ELF32_PROGRAM_HEADER_SIZE, ELF64_HEADER_SIZE,
    ELF64_PROGRAM_HEADER_SIZE, ELF_IDENT_SIZE,
};
use crate::{
    error::{ErrorContext, HeaderField, LoadErrorKind},
    LoadError, LoadResult,
};
use goblin::elf::header::{
    EI_CLASS, EI_DATA, EI_VERSION, ELFCLASS32, ELFCLASS64, ELFDATA2LSB, ELFDATA2MSB, ELFMAG,
    EM_AARCH64, EM_RISCV, ET_DYN, ET_EXEC, EV_CURRENT,
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

pub(crate) struct ElfHeaderInfo {
    class: ElfClass,
    endian: ElfData,
    r#type: ElfType,
    machine: ElfMachine,
    entry: u64,
    program_header_offset: u64,
    program_header_entry_size: u16,
    program_header_count: u16,
    flags: u32,
}

impl ElfHeaderInfo {
    /// Decode the ELF format identification before reading the full header.
    pub(crate) fn decode_ident(ident: &[u8; ELF_IDENT_SIZE]) -> LoadResult<(ElfClass, ElfData)> {
        if ident[..ELFMAG.len()] != ELFMAG[..] {
            return Err(bad_header(HeaderField::Magic, 0));
        }
        let class = match ident[EI_CLASS] {
            ELFCLASS32 => ElfClass::Elf32,
            ELFCLASS64 => ElfClass::Elf64,
            value => return Err(bad_header(HeaderField::Class, u64::from(value))),
        };
        let endian = match ident[EI_DATA] {
            ELFDATA2LSB => ElfData::Little,
            ELFDATA2MSB => ElfData::Big,
            value => return Err(bad_header(HeaderField::Endian, u64::from(value))),
        };
        if ident[EI_VERSION] != EV_CURRENT {
            return Err(bad_header(
                HeaderField::Version,
                u64::from(ident[EI_VERSION]),
            ));
        }
        Ok((class, endian))
    }

    /// Decode the class-specific header fields and validate their structure.
    pub(crate) fn decode(bytes: &[u8], class: ElfClass, endian: ElfData) -> LoadResult<Self> {
        let r#type = match read_u16(bytes, 16, endian)? {
            ET_DYN => ElfType::Dyn,
            ET_EXEC => ElfType::Exec,
            value => ElfType::Other(value),
        };
        let machine = match read_u16(bytes, 18, endian)? {
            EM_RISCV => ElfMachine::Riscv,
            EM_AARCH64 => ElfMachine::Aarch64,
            value => ElfMachine::Other(value),
        };
        let version = read_u32(bytes, 20, endian)?;
        if version != u32::from(EV_CURRENT) {
            return Err(bad_header(HeaderField::Version, u64::from(version)));
        }

        let (
            entry,
            program_header_offset,
            flags,
            header_size,
            program_header_entry_size,
            program_header_count,
        ) = match class {
            ElfClass::Elf32 => (
                u64::from(read_u32(bytes, 24, endian)?),
                u64::from(read_u32(bytes, 28, endian)?),
                read_u32(bytes, 36, endian)?,
                read_u16(bytes, 40, endian)?,
                read_u16(bytes, 42, endian)?,
                read_u16(bytes, 44, endian)?,
            ),
            ElfClass::Elf64 => (
                read_u64(bytes, 24, endian)?,
                read_u64(bytes, 32, endian)?,
                read_u32(bytes, 48, endian)?,
                read_u16(bytes, 52, endian)?,
                read_u16(bytes, 54, endian)?,
                read_u16(bytes, 56, endian)?,
            ),
        };
        let expected_header_size = match class {
            ElfClass::Elf32 => ELF32_HEADER_SIZE as u16,
            ElfClass::Elf64 => ELF64_HEADER_SIZE as u16,
        };
        if header_size != expected_header_size {
            return Err(bad_header(HeaderField::HeaderSize, u64::from(header_size)));
        }
        let expected_ph_entry_size = match class {
            ElfClass::Elf32 => ELF32_PROGRAM_HEADER_SIZE,
            ElfClass::Elf64 => ELF64_PROGRAM_HEADER_SIZE,
        };
        if usize::from(program_header_entry_size) != expected_ph_entry_size {
            return Err(bad_header(
                HeaderField::ProgramHeaderSize,
                u64::from(program_header_entry_size),
            ));
        }

        Ok(Self::new(
            class,
            endian,
            r#type,
            machine,
            entry,
            program_header_offset,
            program_header_entry_size,
            program_header_count,
            flags,
        ))
    }

    #[inline]
    pub const fn new(
        class: ElfClass,
        endian: ElfData,
        r#type: ElfType,
        machine: ElfMachine,
        entry: u64,
        program_header_offset: u64,
        program_header_entry_size: u16,
        program_header_count: u16,
        flags: u32,
    ) -> Self {
        Self {
            class,
            endian,
            r#type,
            machine,
            entry,
            program_header_offset,
            program_header_entry_size,
            program_header_count,
            flags,
        }
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
    pub const fn r#type(&self) -> ElfType {
        self.r#type
    }

    #[inline]
    pub const fn machine(&self) -> ElfMachine {
        self.machine
    }

    #[inline]
    pub const fn entry(&self) -> u64 {
        self.entry
    }

    #[inline]
    pub const fn program_header_offset(&self) -> u64 {
        self.program_header_offset
    }

    #[inline]
    pub const fn program_header_entry_size(&self) -> u16 {
        self.program_header_entry_size
    }

    #[inline]
    pub const fn program_header_count(&self) -> u16 {
        self.program_header_count
    }

    #[inline]
    pub const fn flags(&self) -> u32 {
        self.flags
    }
}

fn bad_header(field: HeaderField, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::HeaderField { field, value },
    )
}
