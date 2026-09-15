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

mod header;
mod program_header;
mod segment;

use goblin::{elf32, elf64};
pub(crate) use header::ElfHeaderInfo;
pub(crate) use program_header::ProgramHeaderInfo;
pub(crate) use segment::{DynamicSegmentInfo, LoadSegmentInfo};

pub(crate) const ELF32_HEADER_SIZE: usize = elf32::header::SIZEOF_EHDR;
pub(crate) const ELF64_HEADER_SIZE: usize = elf64::header::SIZEOF_EHDR;
pub(crate) const ELF_IDENT_SIZE: usize = 16;
pub(crate) const ELF32_PROGRAM_HEADER_SIZE: usize = elf32::program_header::SIZEOF_PHDR;
pub(crate) const ELF64_PROGRAM_HEADER_SIZE: usize = elf64::program_header::SIZEOF_PHDR;

pub(crate) const DT_RELRSZ: u64 = 35;
pub(crate) const DT_RELR: u64 = 36;
pub(crate) const DT_RELRENT: u64 = 37;
