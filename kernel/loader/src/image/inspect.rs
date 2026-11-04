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

//! Checked program headers and read-only planning of executable image layouts.

use super::{admit::program_header_error, plan::PlannedImage};
use crate::{
    elf::{ElfHeaderInfo, LoadSegmentInfo, ProgramHeaderInfo},
    error::{ErrorContext, HeaderField, LoadErrorKind, LoadStage, ProgramHeaderField},
    memory::{address::FileRange, MemoryPermissions, TargetAddress, TargetRange},
    profile::{ElfClass, LoadRequest},
    reader::ElfReader,
    LoadError, LoadResult,
};
use alloc::vec::Vec;
use goblin::elf::program_header::{PT_GNU_RELRO, PT_LOAD};

/// Checked file metadata; image layout and backing have not been prepared yet.
#[must_use = "retain the inspected image for the next loading stage"]
pub(crate) struct InspectedImage<R: ElfReader> {
    pub(super) reader: R,
    pub(super) request: LoadRequest,
    pub(super) header: ElfHeaderInfo,
    pub(super) program_headers: Vec<ProgramHeaderInfo>,
}

impl<R: ElfReader> InspectedImage<R> {
    pub(crate) const fn header(&self) -> &ElfHeaderInfo {
        &self.header
    }

    pub(crate) fn program_headers(&self) -> &[ProgramHeaderInfo] {
        &self.program_headers
    }

    /// Plan the logical layout without reading segment contents or reserving backing.
    pub fn plan(self) -> LoadResult<PlannedImage<R>> {
        self.plan_inner()
            .map_err(|error| error.at_stage(LoadStage::Plan))
    }

    fn plan_inner(self) -> LoadResult<PlannedImage<R>> {
        // Empty PT_LOAD entries were counted during inspection, but contribute
        // no mapping, permissions or alignment to the executable layout.
        let count = self
            .program_headers
            .iter()
            .filter(|header| header.r#type() == PT_LOAD && header.memory_size() != 0)
            .count();
        if count == 0 {
            return Err(LoadError::new(LoadErrorKind::BadElf, ErrorContext::None));
        }
        let mut segments = Vec::new();
        segments
            .try_reserve_exact(count)
            .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        let mut max_alignment = 1;
        for (index, header) in self.program_headers.iter().enumerate() {
            if header.r#type() != PT_LOAD || header.memory_size() == 0 {
                continue;
            }
            // The table count is a u16 and was bounded during admission.
            let index = index as u16;
            let alignment = match header.align() {
                0 | 1 => 1,
                value if value.is_power_of_two() => value,
                value => {
                    return Err(program_header_error(
                        index,
                        ProgramHeaderField::Align,
                        value,
                        LoadErrorKind::InvalidAlignment,
                    ))
                }
            };
            self.request.limits().check_segment_alignment(alignment)?;
            if header.file_offset() % alignment != header.vaddr().get() % alignment {
                return Err(program_header_error(
                    index,
                    ProgramHeaderField::Align,
                    alignment,
                    LoadErrorKind::BadElf,
                ));
            }
            check_target_range(
                TargetRange::new(header.vaddr(), header.memory_size()),
                self.header.class(),
            )?;
            let permissions = self
                .request
                .profile()
                .check_segment_permissions(index, header.flags())?;
            max_alignment = max_alignment.max(alignment);
            segments.push(LoadSegmentInfo::new(
                index,
                FileRange::new(header.file_offset(), header.file_size()),
                header.vaddr(),
                header.memory_size(),
                alignment,
                permissions,
            ));
        }

        segments.sort_unstable_by_key(|segment| segment.vaddr());
        for pair in segments.windows(2) {
            if TargetRange::new(pair[0].vaddr(), pair[0].memory_size())
                .overlaps(TargetRange::new(pair[1].vaddr(), pair[1].memory_size()))
            {
                return Err(program_header_error(
                    pair[1].index(),
                    ProgramHeaderField::VirtualRange,
                    pair[1].vaddr().get(),
                    LoadErrorKind::BadElf,
                ));
            }
        }
        // Nonempty, sorted, disjoint segments have their greatest end last.
        let start = segments[0].vaddr().align_down(max_alignment)?;
        let last = &segments[segments.len() - 1];
        let end = last
            .vaddr()
            .checked_add(last.memory_size())?
            .align_up(max_alignment)?;
        let image_range = TargetRange::new(start, end.checked_sub(start)?);
        check_target_range(image_range, self.header.class())?;
        self.request.limits().check_image_span(image_range.len())?;

        let entry = TargetAddress::new(self.header.entry());
        // These images are executable roots: zero denotes no entry point.
        // Shared-object entry rules are introduced with dynamic metadata.
        if entry.get() == 0 {
            return Err(LoadError::new(
                LoadErrorKind::BadElf,
                ErrorContext::HeaderField {
                    field: HeaderField::Entry,
                    value: 0,
                },
            ));
        }
        let entry_mode = self.request.profile().entry_mode();
        let instruction_alignment = u64::from(entry_mode.instruction_alignment());
        let instruction_size = u64::from(entry_mode.minimum_instruction_size());
        if entry
            .get()
            .checked_rem(instruction_alignment)
            .is_some_and(|remainder| remainder != 0)
        {
            return Err(LoadError::new(
                LoadErrorKind::InvalidAlignment,
                ErrorContext::TargetRange {
                    start: entry,
                    len: instruction_size,
                    align: instruction_alignment,
                },
            ));
        }
        if !segments.iter().any(|segment| {
            segment.permissions().contains(MemoryPermissions::EXECUTE)
                && TargetRange::new(segment.vaddr(), segment.memory_size())
                    .contains_span(entry, instruction_size)
        }) {
            return Err(LoadError::new(
                LoadErrorKind::PermissionConflict,
                ErrorContext::TargetRange {
                    start: entry,
                    len: instruction_size,
                    align: instruction_alignment,
                },
            ));
        }

        if let Some(header) = self
            .program_headers
            .iter()
            .find(|header| header.r#type() == PT_GNU_RELRO)
        {
            let relro = TargetRange::new(header.vaddr(), header.memory_size());
            if !segments.iter().any(|segment| {
                segment.permissions().contains(MemoryPermissions::WRITE)
                    && TargetRange::new(segment.vaddr(), segment.memory_size())
                        .contains_span(relro.start(), relro.len())
            }) {
                return Err(LoadError::new(
                    LoadErrorKind::PermissionConflict,
                    ErrorContext::TargetRange {
                        start: relro.start(),
                        len: relro.len(),
                        align: 0,
                    },
                ));
            }
        }
        Ok(PlannedImage {
            reader: self.reader,
            request: self.request,
            header: self.header,
            program_headers: self.program_headers,
            segments,
            image_range,
            max_alignment,
        })
    }
}

fn check_target_range(range: TargetRange, class: ElfClass) -> LoadResult<()> {
    let end = range.end()?;
    if class == ElfClass::Elf32
        && (range.start().get() > u64::from(u32::MAX) || end.get() > u64::from(u32::MAX))
    {
        return Err(LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::TargetRange {
                start: range.start(),
                len: range.len(),
                align: 0,
            },
        ));
    }
    Ok(())
}
