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

use crate::{
    elf::{ElfHeaderInfo, LoadSegmentInfo, ProgramHeaderInfo},
    memory::{TargetAddress, TargetRange},
    profile::LoadRequest,
    reader::ElfReader,
};
use alloc::vec::Vec;

#[must_use = "retain the layout and its reader for the allocation stage"]
pub(crate) struct PlannedImage<R: ElfReader> {
    pub(super) reader: R,
    pub(super) request: LoadRequest,
    pub(super) header: ElfHeaderInfo,
    pub(super) program_headers: Vec<ProgramHeaderInfo>,
    pub(super) segments: Vec<LoadSegmentInfo>,
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
}
