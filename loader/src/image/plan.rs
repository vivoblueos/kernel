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
    identity::{ElfClass, ElfType, LoadRequest},
    image::{allocate::AllocatedImage, inspect::StackKind},
    memory::{AllocationRequest, ImageAllocation, ImageLoadTransaction, ImageMemory, Placement},
    reader::ElfReader,
};

pub(crate) struct PlannedImage<R: ElfReader> {
    reader: R,
    request: LoadRequest,
    aligned_min_vaddr: TargetAddress,
    image_span: u64,
    max_align: u64,
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

impl<R: ElfReader> PlannedImage<R> {
    #[inline]
    pub const fn new(
        reader: R,
        request: LoadRequest,
        aligned_min_vaddr: TargetAddress,
        image_span: u64,
        max_align: u64,
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
            request,
            aligned_min_vaddr,
            image_span,
            max_align,
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

    fn allocation_request(&self) -> LoadResult<AllocationRequest> {
        let size = self.image_span;
        let align = self.max_align;
        if size == 0 {
            return Err(LoadError::new(
                LoadErrorKind::IncorrectLayout,
                ErrorContext::TargetRange {
                    start: self.aligned_min_vaddr,
                    len: size,
                    align,
                },
            ));
        }
        if !align.is_power_of_two() {
            return Err(LoadError::new(
                LoadErrorKind::InvalidAlignment,
                ErrorContext::TargetRange {
                    start: self.aligned_min_vaddr,
                    len: size,
                    align,
                },
            ));
        }
        let placement = match self.request.profile().r#type() {
            // Movable image: any suitably aligned address works.
            ElfType::Dyn => Placement::Anywhere,
            // Fixed image: the allocation must cover exactly the aligned
            // image span so segment vaddrs map onto themselves (load bias 0).
            ElfType::Exec => Placement::Fixed(TargetRange::new(self.aligned_min_vaddr, size)),
            ElfType::Other(_) => {
                return Err(LoadError::new(
                    LoadErrorKind::UnsupportedByProfile,
                    ErrorContext::None,
                ))
            }
        };
        Ok(AllocationRequest::new(placement, size, align))
    }

    pub fn allocate<M>(self, mut memory: M) -> LoadResult<AllocatedImage<R, M>>
    where
        M: ImageMemory,
    {
        // The allocation stage attaches LoadStage::Allocate to every error
        // leaving this function, including the ones raised by helpers.
        let at_allocate = |error: LoadError| error.at_stage(LoadStage::Allocate);

        let request = self.allocation_request().map_err(at_allocate)?;
        let lease = memory.allocate_image(request).map_err(at_allocate)?;
        let transaction = ImageLoadTransaction::new(memory, lease);

        validate_allocation(
            transaction.allocation(),
            &request,
            self.request.profile().class(),
        )
        .map_err(at_allocate)?;
        let load_bias = TargetAddress::new(
            transaction
                .allocation()
                .base()
                .checked_sub(self.aligned_min_vaddr)
                .map_err(at_allocate)?,
        );
        Ok(AllocatedImage::new(
            self.reader,
            transaction,
            self.aligned_min_vaddr,
            self.max_align,
            load_bias,
            self.request,
            self.entry_vaddr,
            self.canonical_entry_vaddr,
            self.load_segments,
            self.dynamic,
            self.relro,
            self.stack,
            self.interpreter,
            self.tls,
            self.phdr_geometry,
        ))
    }
}

fn validate_allocation(
    allocation: &ImageAllocation,
    request: &AllocationRequest,
    class: ElfClass,
) -> LoadResult<()> {
    let base = allocation.base();
    let aligned = base.get() % request.align() == 0;
    let end = base.checked_add(allocation.len());
    let target_width_valid = end.as_ref().is_ok_and(|end| match class {
        ElfClass::Elf32 => end.get() <= u64::from(u32::MAX),
        ElfClass::Elf64 => true,
    });
    let host_width_valid = end
        .as_ref()
        .is_ok_and(|end| usize::try_from(end.get()).is_ok());
    // Fixed placement must land exactly on the planned image span; the
    // uniform load-bias formula only yields 0 when the base matches.
    let fixed_span_valid = match request.placement() {
        Placement::Fixed(range) => base == range.start() && allocation.len() == range.len(),
        Placement::Anywhere => true,
    };

    if allocation.len() == request.size()
        && allocation.align() == request.align()
        && aligned
        && target_width_valid
        && host_width_valid
        && fixed_span_valid
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
