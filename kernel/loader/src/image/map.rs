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

//! Initialized segments; relocation, cache synchronization and protection follow later.

use crate::{
    elf::{ElfHeaderInfo, LoadSegmentInfo},
    memory::{AllocationOffset, ImageMapping, TargetAddress, TargetRange},
    profile::LoadRequest,
    LoadResult,
};
use alloc::vec::Vec;

#[must_use = "keep the mapped image alive to retain its backing"]
pub(crate) struct MappedImage<A: ImageMapping> {
    pub(super) allocation: A,
    pub(super) request: LoadRequest,
    pub(super) header: ElfHeaderInfo,
    pub(super) segments: Vec<LoadSegmentInfo>,
    /// Original ELF virtual range, retained for protection after relocation.
    pub(super) relro: Option<TargetRange>,
    pub(super) image_range: TargetRange,
    pub(super) entry: TargetAddress,
}

impl<A: ImageMapping> MappedImage<A> {
    pub(crate) const fn allocation(&self) -> &A {
        &self.allocation
    }

    pub(crate) const fn entry(&self) -> TargetAddress {
        self.entry
    }

    /// Signed displacement, including allocations below the ELF's link address.
    pub(crate) fn load_bias(&self) -> i128 {
        i128::from(self.allocation.base().get()) - i128::from(self.image_range.start().get())
    }

    pub(crate) fn read(&self, offset: AllocationOffset, dst: &mut [u8]) -> LoadResult<()> {
        self.allocation.read(offset, dst)
    }
}
