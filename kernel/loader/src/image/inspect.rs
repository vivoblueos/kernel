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

//! Checked program headers retained for the next layout-planning stage.

use crate::{
    elf::{ElfHeaderInfo, ProgramHeaderInfo},
    profile::LoadRequest,
    reader::ElfReader,
};
use alloc::vec::Vec;

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
}
