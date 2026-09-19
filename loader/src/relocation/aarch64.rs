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

use goblin::elf::reloc::{
    R_AARCH64_ABS64, R_AARCH64_GLOB_DAT, R_AARCH64_JUMP_SLOT, R_AARCH64_RELATIVE,
};

use crate::{
    identity::{ElfClass, ElfMachine},
    relocation::{AddendEncoding, ArchRelocator, RelocationKind},
};

#[derive(Clone, Copy)]
pub struct AArch64Relocator;

impl ArchRelocator for AArch64Relocator {
    fn machine(&self) -> ElfMachine {
        ElfMachine::Aarch64
    }

    fn class(&self) -> ElfClass {
        ElfClass::Elf64
    }

    fn relative_type(&self) -> u32 {
        R_AARCH64_RELATIVE
    }

    fn addend_encoding(&self) -> AddendEncoding {
        AddendEncoding::Explicit
    }

    fn classify_relocation(&self, raw_type: u32) -> Option<RelocationKind> {
        match raw_type {
            R_AARCH64_RELATIVE => Some(RelocationKind::Relative),
            R_AARCH64_ABS64 => Some(RelocationKind::Absolute),
            R_AARCH64_GLOB_DAT => Some(RelocationKind::GlobalData),
            R_AARCH64_JUMP_SLOT => Some(RelocationKind::JumpSlot),
            _ => None,
        }
    }
}
