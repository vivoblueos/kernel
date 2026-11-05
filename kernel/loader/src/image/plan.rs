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

//! Validated single-image layout; no backing has been reserved or modified.

use super::allocate::AllocatedImage;
use crate::{
    elf::{ElfHeaderInfo, LoadSegmentInfo},
    error::{ErrorContext, LoadErrorKind, LoadStage},
    memory::{
        AllocationOffset, ImageLayout, ImageMapping, ImageMemory, Placement, SegmentLayout,
        TargetAddress, TargetRange,
    },
    profile::{ElfClass, ElfType, LoadRequest},
    reader::ElfReader,
    LoadError, LoadResult,
};
use alloc::vec::Vec;

#[must_use = "retain the layout and its reader for the allocation stage"]
pub(crate) struct PlannedImage<R: ElfReader> {
    pub(super) reader: R,
    pub(super) request: LoadRequest,
    pub(super) header: ElfHeaderInfo,
    pub(super) segments: Vec<LoadSegmentInfo>,
    /// Validated ELF virtual range; write protection is applied after relocation.
    pub(super) relro: Option<TargetRange>,
    pub(super) image_range: TargetRange,
    pub(super) max_alignment: u64,
}

impl<R: ElfReader> PlannedImage<R> {
    pub(crate) fn segments(&self) -> &[LoadSegmentInfo] {
        &self.segments
    }

    pub(crate) const fn image_range(&self) -> TargetRange {
        self.image_range
    }

    pub(crate) const fn max_alignment(&self) -> u64 {
        self.max_alignment
    }

    pub(crate) fn entry(&self) -> TargetAddress {
        TargetAddress::new(self.header.entry())
    }

    fn image_layout(&self) -> LoadResult<ImageLayout> {
        let placement = match self.header.r#type() {
            ElfType::Dyn => Placement::Anywhere,
            ElfType::Exec => Placement::Fixed(self.image_range),
            ElfType::Other(_) => {
                return Err(LoadError::new(
                    LoadErrorKind::UnsupportedByProfile,
                    ErrorContext::None,
                ))
            }
        };
        let mut segments = Vec::new();
        segments
            .try_reserve_exact(self.segments.len())
            .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        for segment in &self.segments {
            segments.push(SegmentLayout::new(
                AllocationOffset::new(segment.vaddr().checked_sub(self.image_range.start())?),
                segment.memory_size(),
                segment.permissions(),
            ));
        }
        ImageLayout::new(
            placement,
            self.image_range.len(),
            self.max_alignment,
            segments,
        )
    }

    pub(crate) fn allocate<M: ImageMemory>(
        self,
        memory: M,
    ) -> LoadResult<AllocatedImage<R, M::Allocation>> {
        self.allocate_inner(memory)
            .map_err(|error| error.at_stage(LoadStage::Allocate))
    }

    fn allocate_inner<M: ImageMemory>(
        self,
        mut memory: M,
    ) -> LoadResult<AllocatedImage<R, M::Allocation>> {
        let layout = self.image_layout()?;
        let allocation = memory.prepare_image(&layout)?;
        // The returned mapping already owns cleanup, including when its
        // metadata fails validation below.
        validate_allocation(&allocation, &layout, self.header.class())?;
        Ok(AllocatedImage {
            reader: self.reader,
            allocation,
            request: self.request,
            header: self.header,
            segments: self.segments,
            relro: self.relro,
            image_range: self.image_range,
        })
    }
}

fn validate_allocation(
    allocation: &impl ImageMapping,
    layout: &ImageLayout,
    class: ElfClass,
) -> LoadResult<()> {
    let base = allocation.base();
    let target_width_valid = base
        .checked_add(allocation.len())
        .is_ok_and(|end| class == ElfClass::Elf64 || end.get() <= u64::from(u32::MAX));
    let fixed_valid = match layout.placement() {
        Placement::Anywhere => true,
        Placement::Fixed(range) => base == range.start(),
    };
    // Only the backend may require host pointer representability. A target
    // VA may refer to another address space or exceed the loader's host width.
    if allocation.len() == layout.size()
        && allocation.align() == layout.align()
        && base.get().checked_rem(layout.align()) == Some(0)
        && target_width_valid
        && fixed_valid
    {
        return Ok(());
    }
    Err(LoadError::new(
        LoadErrorKind::Backend,
        ErrorContext::Allocation {
            base,
            len: allocation.len(),
            align: allocation.align(),
        },
    ))
}
