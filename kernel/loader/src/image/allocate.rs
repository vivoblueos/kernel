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

//! Populate prepared segment backing through the memory backend.

use super::map::MappedImage;
use crate::{
    elf::{ElfHeaderInfo, LoadSegmentInfo},
    error::{ErrorContext, LoadErrorKind, LoadStage},
    memory::{AllocationOffset, ImageMapping, TargetAddress, TargetRange},
    profile::LoadRequest,
    reader::ElfReader,
    LoadError, LoadResult,
};
use alloc::vec::Vec;

const COPY_BUFFER_SIZE: usize = 512;

#[must_use = "dropping a prepared image releases its allocation"]
pub(crate) struct AllocatedImage<R: ElfReader, A: ImageMapping> {
    pub(super) reader: R,
    pub(super) allocation: A,
    pub(super) request: LoadRequest,
    pub(super) header: ElfHeaderInfo,
    pub(super) segments: Vec<LoadSegmentInfo>,
    pub(super) relro: Option<TargetRange>,
    pub(super) image_range: TargetRange,
}

impl<R: ElfReader, A: ImageMapping> AllocatedImage<R, A> {
    pub(crate) fn map(self) -> LoadResult<MappedImage<A>> {
        self.map_inner()
            .map_err(|error| error.at_stage(LoadStage::Map))
    }

    fn map_inner(mut self) -> LoadResult<MappedImage<A>> {
        let base = self.allocation.base();
        let entry_offset =
            TargetAddress::new(self.header.entry()).checked_sub(self.image_range.start())?;
        let entry = base.checked_add(entry_offset)?;
        let entry_mode = self.request.profile().entry_mode();
        let instruction_alignment = u64::from(entry_mode.instruction_alignment());
        // p_align may be weaker than instruction alignment. Check the actual
        // relocated entry before any bytes are read or destinations modified.
        if entry
            .get()
            .checked_rem(instruction_alignment)
            .is_some_and(|remainder| remainder != 0)
        {
            return Err(LoadError::new(
                LoadErrorKind::InvalidAlignment,
                ErrorContext::TargetRange {
                    start: entry,
                    len: u64::from(entry_mode.minimum_instruction_size()),
                    align: instruction_alignment,
                },
            ));
        }
        let mut scratch = [0; COPY_BUFFER_SIZE];
        for segment in &self.segments {
            let offset =
                AllocationOffset::new(segment.vaddr().checked_sub(self.image_range.start())?);
            let file = segment.file_range();
            let mut copied = 0;
            while copied < file.len() {
                let len = (file.len() - copied).min(COPY_BUFFER_SIZE as u64) as usize;
                let file_offset = file.offset().checked_add(copied).ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::IntegerOverflow,
                        ErrorContext::FileRange {
                            offset: file.offset(),
                            len: file.len(),
                            file_len: 0,
                        },
                    )
                })?;
                self.reader
                    .read_exact_at(file_offset, &mut scratch[..len])?;
                self.allocation
                    .write(offset.checked_add(copied)?, &scratch[..len])?;
                copied += len as u64;
            }
            let bss_len = segment
                .memory_size()
                .checked_sub(file.len())
                .ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::BadElf,
                        ErrorContext::TargetRange {
                            start: segment.vaddr(),
                            len: segment.memory_size(),
                            align: segment.align(),
                        },
                    )
                })?;
            if bss_len != 0 {
                self.allocation
                    .zero(offset.checked_add(file.len())?, bss_len)?;
            }
        }
        Ok(MappedImage {
            allocation: self.allocation,
            request: self.request,
            header: self.header,
            segments: self.segments,
            relro: self.relro,
            image_range: self.image_range,
            entry,
        })
    }
}
