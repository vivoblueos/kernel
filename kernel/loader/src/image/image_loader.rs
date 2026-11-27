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

use goblin::elf::header::{EI_ABIVERSION, EI_OSABI};

use crate::{
    elf::{ElfClass, ElfHeaderInfo, ELF32_HEADER_SIZE, ELF64_HEADER_SIZE, ELF_IDENT_SIZE},
    error::{ErrorContext, HeaderField, LoadErrorKind, LoadStage},
    image::admit::AdmittedImage,
    profile::{LoadLimits, LoadProfile},
    reader::ElfReader,
    LoadError, LoadResult,
};

/// Parameters for one single-image loading attempt.
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

/// Begin read-only ELF validation using any positional reader.
#[must_use = "consume the loader with admit() to validate the ELF header"]
pub(crate) struct ImageLoader<R: ElfReader> {
    reader: R,
    request: LoadRequest,
}

impl<R: ElfReader> ImageLoader<R> {
    #[inline]
    pub const fn new(reader: R, request: LoadRequest) -> Self {
        Self { reader, request }
    }

    /// Validate the ELF header and bound the program-header table before inspection.
    pub fn admit(self) -> LoadResult<AdmittedImage<R>> {
        self.admit_inner()
            .map_err(|error| error.at_stage(LoadStage::Admit))
    }

    fn admit_inner(self) -> LoadResult<AdmittedImage<R>> {
        let file_len = self.reader.len()?;
        self.request.limits().check_file_len(file_len)?;

        let mut ident = [0; ELF_IDENT_SIZE];
        self.reader.read_exact_at(0, &mut ident)?;
        let (class, endian) = ElfHeaderInfo::decode_ident(&ident)?;
        self.request
            .profile()
            .check_ident_abi(ident[EI_OSABI], ident[EI_ABIVERSION])?;
        let header_size = match class {
            ElfClass::Elf32 => ELF32_HEADER_SIZE,
            ElfClass::Elf64 => ELF64_HEADER_SIZE,
        };
        let mut bytes = [0; ELF64_HEADER_SIZE];
        self.reader.read_exact_at(0, &mut bytes[..header_size])?;
        let header = ElfHeaderInfo::decode(&bytes[..header_size], class, endian)?;
        self.request.profile().check_header(&header)?;
        validate_program_header_table(&header, self.request.limits(), file_len)?;
        Ok(AdmittedImage::new(
            self.reader,
            header,
            self.request,
            file_len,
        ))
    }
}

fn validate_program_header_table(
    header: &ElfHeaderInfo,
    limits: &LoadLimits,
    file_len: u64,
) -> LoadResult<()> {
    limits.check_program_header_count(header.program_header_count())?;

    let header_size = match header.class() {
        ElfClass::Elf32 => ELF32_HEADER_SIZE,
        ElfClass::Elf64 => ELF64_HEADER_SIZE,
    };
    if header.program_header_count() != 0 && header.program_header_offset() < header_size as u64 {
        return Err(bad_header(
            HeaderField::ProgramHeaderTable,
            header.program_header_offset(),
        ));
    }

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

fn bad_header(field: HeaderField, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::HeaderField { field, value },
    )
}
