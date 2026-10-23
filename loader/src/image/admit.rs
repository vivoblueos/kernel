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

//! Program-header inspection without mapping or writing image backing.

use alloc::vec::Vec;
use goblin::elf::program_header::{
    PT_DYNAMIC, PT_GNU_RELRO, PT_GNU_STACK, PT_LOAD, PT_NULL, PT_PHDR,
};

use crate::{
    elf::{ElfHeaderInfo, ProgramHeaderInfo, ELF64_PROGRAM_HEADER_SIZE},
    error::{ErrorContext, LoadErrorKind, LoadStage, ProgramHeaderField},
    image::inspect::InspectedImage,
    profile::LoadRequest,
    reader::ElfReader,
    LoadError, LoadResult,
};

/// An admitted ELF header retaining its reader for program-header inspection.
#[must_use = "consume the admitted image with inspect() to validate program headers"]
pub(crate) struct AdmittedImage<R: ElfReader> {
    reader: R,
    header: ElfHeaderInfo,
    request: LoadRequest,
    file_len: u64,
}

impl<R: ElfReader> AdmittedImage<R> {
    pub(crate) const fn new(
        reader: R,
        header: ElfHeaderInfo,
        request: LoadRequest,
        file_len: u64,
    ) -> Self {
        Self {
            reader,
            header,
            request,
            file_len,
        }
    }

    pub(crate) const fn header(&self) -> &ElfHeaderInfo {
        &self.header
    }

    pub fn inspect(self) -> LoadResult<InspectedImage<R>> {
        self.inspect_inner()
            .map_err(|error| error.at_stage(LoadStage::Inspect))
    }

    fn inspect_inner(self) -> LoadResult<InspectedImage<R>> {
        let count = self.header.program_header_count();
        let mut program_headers: Vec<ProgramHeaderInfo> = Vec::new();
        program_headers
            .try_reserve_exact(usize::from(count))
            .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        let entry_size = usize::from(self.header.program_header_entry_size());
        let mut raw = [0; ELF64_PROGRAM_HEADER_SIZE];
        let mut seen_singletons = 0u8;

        for index in 0..count {
            // Admission checked this complete table's extent and entry size.
            let offset = self.header.program_header_offset()
                + u64::from(index) * u64::from(self.header.program_header_entry_size());
            self.reader.read_exact_at(offset, &mut raw[..entry_size])?;
            let header = ProgramHeaderInfo::decode(
                &raw[..entry_size],
                self.header.class(),
                self.header.endian(),
            )?;
            let kind = header.r#type();

            self.request.profile().check_program_header(index, kind)?;

            // PT_NULL marks an unused entry; its other members are undefined.
            if kind == PT_NULL {
                program_headers.push(header);
                continue;
            }
            let singleton = match kind {
                PT_DYNAMIC => Some((0b0001, ProgramHeaderField::DuplicateDynamic)),
                PT_PHDR => Some((0b0010, ProgramHeaderField::DuplicatePhdr)),
                PT_GNU_RELRO => Some((0b0100, ProgramHeaderField::DuplicateRelro)),
                PT_GNU_STACK => Some((0b1000, ProgramHeaderField::DuplicateStack)),
                _ => None,
            };
            if let Some((bit, field)) = singleton {
                if seen_singletons & bit != 0 {
                    return Err(program_header_error(
                        index,
                        field,
                        u64::from(kind),
                        LoadErrorKind::BadElf,
                    ));
                }
                seen_singletons |= bit;
            }
            if matches!(kind, PT_LOAD | PT_DYNAMIC) && header.file_size() > header.memory_size() {
                return Err(program_header_error(
                    index,
                    ProgramHeaderField::FileRange,
                    header.file_size(),
                    LoadErrorKind::BadElf,
                ));
            }
            let context = || ErrorContext::FileRange {
                offset: header.file_offset(),
                len: header.file_size(),
                file_len: self.file_len,
            };
            let end = header
                .file_offset()
                .checked_add(header.file_size())
                .ok_or_else(|| LoadError::new(LoadErrorKind::IntegerOverflow, context()))?;
            if end > self.file_len {
                return Err(LoadError::new(LoadErrorKind::OutOfBounds, context()));
            }
            header
                .vaddr()
                .checked_add(header.memory_size())
                .ok_or_else(|| {
                    program_header_error(
                        index,
                        ProgramHeaderField::VirtualRange,
                        header.vaddr(),
                        LoadErrorKind::IntegerOverflow,
                    )
                })?;
            if kind == PT_GNU_STACK {
                self.request
                    .profile()
                    .check_stack_flags(index, header.flags())?;
            }
            program_headers.push(header);
        }

        Ok(InspectedImage {
            reader: self.reader,
            request: self.request,
            header: self.header,
            program_headers,
        })
    }
}

fn program_header_error(
    index: u16,
    field: ProgramHeaderField,
    value: u64,
    kind: LoadErrorKind,
) -> LoadError {
    LoadError::new(
        kind,
        ErrorContext::ProgramHeader {
            index,
            field,
            value,
        },
    )
}
