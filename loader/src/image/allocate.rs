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
    dynamic_linker::ProgramHeaderGeometry,
    elf::{DynamicSegmentInfo, LoadSegmentInfo},
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::LoadRequest,
    image::{
        inspect::StackKind,
        map::{LoadedRegion, MappedImage},
    },
    memory::{AllocationOffset, ImageLoadTransaction, ImageMemory},
    reader::ElfReader,
};

const COPY_BUFFER_SIZE: usize = 512;

#[must_use = "dropping a reserved image aborts its allocation"]
pub(crate) struct AllocatedImage<R: ElfReader, M: ImageMemory> {
    reader: R,
    transaction: ImageLoadTransaction<M>,
    aligned_min_vaddr: TargetAddress,
    max_align: u64,
    load_bias: TargetAddress,
    request: LoadRequest,
    entry_vaddr: TargetAddress,
    canonical_entry_vaddr: TargetAddress,
    load_segments: Vec<LoadSegmentInfo>,
    dynamic: Option<DynamicSegmentInfo>,
    relro: Option<TargetRange>,
    stack: StackKind,
    interpreter: Option<FileRange>,
    tls: Option<TargetRange>,
    phdr_geometry: ProgramHeaderGeometry,
}

impl<R: ElfReader, M: ImageMemory> AllocatedImage<R, M> {
    #[inline]
    pub fn new(
        reader: R,
        transaction: ImageLoadTransaction<M>,
        aligned_min_vaddr: TargetAddress,
        max_align: u64,
        load_bias: TargetAddress,
        request: LoadRequest,
        entry_vaddr: TargetAddress,
        canonical_entry_vaddr: TargetAddress,
        load_segments: Vec<LoadSegmentInfo>,
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
            aligned_min_vaddr,
            max_align,
            load_bias,
            request,
            entry_vaddr,
            canonical_entry_vaddr,
            load_segments,
            dynamic,
            relro,
            stack,
            interpreter,
            tls,
            phdr_geometry,
        }
    }

    pub fn map(mut self) -> LoadResult<MappedImage<R, M>> {
        let mut regions = Vec::new();
        regions
            .try_reserve_exact(self.load_segments.len())
            .map_err(|_| {
                LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
                    .at_stage(LoadStage::Map)
            })?;

        for segment in self.load_segments.iter() {
            let allocation_offset = segment
                .vaddr()
                .checked_sub(self.aligned_min_vaddr)
                .map_err(|error| error.at_stage(LoadStage::Map))?;
            let runtime_start = self
                .load_bias
                .checked_add(segment.vaddr().get())
                .map_err(|error| error.at_stage(LoadStage::Map))?;
            let runtime_range = TargetRange::new(runtime_start, segment.memory_size());
            runtime_range
                .end()
                .map_err(|error| error.at_stage(LoadStage::Map))?;
            regions.push(LoadedRegion::new(
                TargetRange::new(segment.vaddr(), segment.memory_size()),
                runtime_range,
                segment.file_range(),
                AllocationOffset::new(allocation_offset),
            ));
        }

        let entry = self
            .load_bias
            .checked_add(self.entry_vaddr.get())
            .map_err(|error| error.at_stage(LoadStage::Map))?;
        let canonical_entry = self
            .load_bias
            .checked_add(self.canonical_entry_vaddr.get())
            .map_err(|error| error.at_stage(LoadStage::Map))?;

        let mut scratch = [0; COPY_BUFFER_SIZE];
        for region in regions.iter() {
            let offset = region.allocation_offset();
            let file_range = region.file_range();
            let mut copied = 0;
            while copied < file_range.len() {
                let remaining = file_range.len() - copied;
                let chunk_len = core::cmp::min(remaining, COPY_BUFFER_SIZE as u64) as usize;
                self.reader
                    .read_exact_at(
                        file_range.offset().checked_add(copied).ok_or_else(|| {
                            LoadError::new(
                                LoadErrorKind::IntegerOverflow,
                                ErrorContext::FileRange {
                                    offset: file_range.offset(),
                                    len: file_range.len(),
                                    file_len: 0,
                                },
                            )
                            .at_stage(LoadStage::Map)
                        })?,
                        &mut scratch[..chunk_len],
                    )
                    .map_err(|error| error.at_stage(LoadStage::Map))?;
                self.transaction
                    .write(
                        region
                            .allocation_offset()
                            .checked_add(copied)
                            .map_err(|error| error.at_stage(LoadStage::Map))?,
                        &scratch[..chunk_len],
                    )
                    .map_err(|error| error.at_stage(LoadStage::Map))?;
                copied += chunk_len as u64;
            }
            let bss_len = region
                .vaddr_range()
                .len()
                .checked_sub(region.file_range().len())
                .ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::OutOfBounds,
                        ErrorContext::TargetRange {
                            start: region.vaddr_range().start(),
                            len: region.vaddr_range().len(),
                            align: self.max_align,
                        },
                    )
                    .at_stage(LoadStage::Map)
                })?;
            let bss_offset = offset
                .checked_add(region.file_range().len())
                .map_err(|error| error.at_stage(LoadStage::Map))?;
            if bss_len != 0 {
                self.transaction
                    .zero(bss_offset, bss_len)
                    .map_err(|error| error.at_stage(LoadStage::Map))?;
            }
        }
        Ok(MappedImage::new(
            self.reader,
            self.transaction,
            self.load_bias,
            self.request,
            entry,
            canonical_entry,
            self.load_segments,
            regions,
            self.dynamic,
            self.relro,
            self.stack,
            self.interpreter,
            self.tls,
            self.phdr_geometry,
        ))
    }
}
