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

use goblin::elf::reloc::{R_ARM_ABS32, R_ARM_GLOB_DAT, R_ARM_JUMP_SLOT, R_ARM_RELATIVE};

use crate::{
    identity::{ElfClass, ElfMachine},
    relocation::{AddendEncoding, ArchRelocator, RelocationKind},
};

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ArmRelocator;

impl ArchRelocator for ArmRelocator {
    fn machine(&self) -> ElfMachine {
        ElfMachine::Arm
    }

    fn class(&self) -> super::ElfClass {
        ElfClass::Elf32
    }

    fn relative_type(&self) -> u32 {
        R_ARM_RELATIVE
    }

    fn addend_encoding(&self) -> super::AddendEncoding {
        AddendEncoding::Implicit
    }

    fn classify_relocation(&self, raw_type: u32) -> Option<RelocationKind> {
        match raw_type {
            R_ARM_RELATIVE => Some(RelocationKind::Relative),
            R_ARM_ABS32 => Some(RelocationKind::Absolute),
            R_ARM_GLOB_DAT => Some(RelocationKind::GlobalData),
            R_ARM_JUMP_SLOT => Some(RelocationKind::JumpSlot),
            _ => None,
        }
    }
}
