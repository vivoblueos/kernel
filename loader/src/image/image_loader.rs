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

use goblin::elf::header::{
    EI_CLASS, EI_DATA, EI_OSABI, EI_VERSION, ELFCLASS32, ELFCLASS64, ELFDATA2LSB, ELFDATA2MSB,
    ELFMAG, ELFOSABI_NONE, EM_AARCH64, EM_ARM, EM_RISCV, ET_DYN, ET_EXEC, EV_CURRENT,
};

use crate::{
    elf::{
        ElfHeaderInfo, ELF32_HEADER_SIZE, ELF32_PROGRAM_HEADER_SIZE, ELF64_HEADER_SIZE,
        ELF64_PROGRAM_HEADER_SIZE, ELF_IDENT_SIZE,
    },
    error::{ErrorContext, HeaderField, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::{ElfClass, ElfData, ElfMachine, ElfType, LoadRequest},
    image::admit::AdmittedImage,
    reader::ElfReader,
};

pub(crate) struct ImageLoader<R: ElfReader> {
    reader: R,
    request: LoadRequest,
}

impl<R: ElfReader> ImageLoader<R> {
    #[inline]
    pub const fn new(reader: R, request: LoadRequest) -> Self {
        Self { reader, request }
    }

    pub fn admit(self) -> LoadResult<AdmittedImage<R>> {
        // The admit stage attaches LoadStage::Admit to every error leaving
        // this function, including the ones raised by helpers.
        let file_len = at_admit(self.reader.len())?;
        at_admit(self.request.limits().check_file_len(file_len))?;

        let mut ident = [0; ELF_IDENT_SIZE];
        at_admit(self.reader.read_exact_at(0, &mut ident))?;
        let (class, endian) = at_admit(validate_ident(&ident))?;
        let header_size = match class {
            ElfClass::Elf32 => ELF32_HEADER_SIZE,
            ElfClass::Elf64 => ELF64_HEADER_SIZE,
        };
        let mut bytes = [0; ELF64_HEADER_SIZE];
        at_admit(self.reader.read_exact_at(0, &mut bytes[..header_size]))?;
        let header = at_admit(decode_header(&bytes[..header_size], class, endian))?;
        at_admit(validate_header(&header, &self.request, file_len))?;
        Ok(AdmittedImage::new(
            self.reader,
            header,
            self.request,
            file_len,
        ))
    }
}

fn validate_ident(ident: &[u8; ELF_IDENT_SIZE]) -> LoadResult<(ElfClass, ElfData)> {
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
    if ident[EI_OSABI] != ELFOSABI_NONE {
        return Err(unsupported_header(
            HeaderField::OsAbi,
            u64::from(ident[EI_OSABI]),
        ));
    }
    Ok((class, endian))
}

fn decode_header(bytes: &[u8], class: ElfClass, endian: ElfData) -> LoadResult<ElfHeaderInfo> {
    let r#type = match read_u16(bytes, 16, endian)? {
        ET_DYN => ElfType::Dyn,
        ET_EXEC => ElfType::Exec,
        value => ElfType::Other(value),
    };
    let machine = match read_u16(bytes, 18, endian)? {
        EM_ARM => ElfMachine::Arm,
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

    Ok(ElfHeaderInfo::new(
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

fn validate_header(header: &ElfHeaderInfo, request: &LoadRequest, file_len: u64) -> LoadResult<()> {
    if header.r#type() != request.profile().r#type() {
        return Err(unsupported_header(
            HeaderField::Type,
            u64::from(header.r#type()),
        ));
    }
    if header.class() != request.profile().class() {
        return Err(unsupported_header(
            HeaderField::Class,
            u64::from(header.class()),
        ));
    }
    if header.endian() != request.profile().endian() {
        return Err(unsupported_header(
            HeaderField::Endian,
            u64::from(header.endian()),
        ));
    }
    if header.machine() != request.profile().machine() {
        return Err(unsupported_header(
            HeaderField::Machine,
            u64::from(header.machine()),
        ));
    }
    // `e_flags` is machine-defined; a trusted profile always carries a
    // HeaderFlagsPolicy for its machine, so an unknown ABI/float/RVE
    // combination fails admission before any allocation.
    if !request.profile().header_flags().accepts(header.flags()) {
        return Err(unsupported_header(
            HeaderField::Flags,
            u64::from(header.flags()),
        ));
    }
    request
        .limits()
        .check_program_header_count(header.program_header_count())?;

    let table_len = u64::from(header.program_header_entry_size())
        .checked_mul(u64::from(header.program_header_count()))
        .ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::HeaderField {
                    field: HeaderField::ProgramHeaderTable,
                    value: header.program_header_offset(),
                },
            )
        })?;
    let table_end = header
        .program_header_offset()
        .checked_add(table_len)
        .ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::FileRange {
                    offset: header.program_header_offset(),
                    len: table_len,
                    file_len,
                },
            )
        })?;
    if table_end > file_len {
        return Err(LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::FileRange {
                offset: header.program_header_offset(),
                len: table_len,
                file_len,
            },
        ));
    }
    Ok(())
}

pub(crate) fn read_u16(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u16> {
    let raw = read_array::<2>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u16::from_le_bytes(raw),
        ElfData::Big => u16::from_be_bytes(raw),
    })
}

pub(crate) fn read_u32(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u32> {
    let raw = read_array::<4>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u32::from_le_bytes(raw),
        ElfData::Big => u32::from_be_bytes(raw),
    })
}

pub(crate) fn read_u64(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u64> {
    let raw = read_array::<8>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u64::from_le_bytes(raw),
        ElfData::Big => u64::from_be_bytes(raw),
    })
}

fn read_array<const N: usize>(bytes: &[u8], offset: usize) -> LoadResult<[u8; N]> {
    let end = offset.checked_add(N).ok_or_else(|| {
        LoadError::new(
            LoadErrorKind::IntegerOverflow,
            ErrorContext::FileRange {
                offset: offset as u64,
                len: N as u64,
                file_len: bytes.len() as u64,
            },
        )
    })?;
    let src = bytes.get(offset..end).ok_or_else(|| {
        LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::FileRange {
                offset: offset as u64,
                len: N as u64,
                file_len: bytes.len() as u64,
            },
        )
    })?;
    let mut raw = [0; N];
    raw.copy_from_slice(src);
    Ok(raw)
}

fn at_admit<T>(result: LoadResult<T>) -> LoadResult<T> {
    result.map_err(|error| error.at_stage(LoadStage::Admit))
}

fn bad_header(field: HeaderField, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::HeaderField { field, value },
    )
}

fn unsupported_header(field: HeaderField, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::UnsupportedByProfile,
        ErrorContext::HeaderField { field, value },
    )
}
