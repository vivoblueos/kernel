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

use goblin::elf;

use crate::{
    identity::{ElfClass, ElfMachine},
    relocation::{AddendEncoding, ArchRelocator},
};

#[derive(Clone, Copy)]
pub struct Riscv64Relocator;

#[derive(Clone, Copy)]
pub struct Riscv32Relocator;

impl ArchRelocator for Riscv64Relocator {
    fn machine(&self) -> super::ElfMachine {
        ElfMachine::Riscv
    }

    fn class(&self) -> super::ElfClass {
        ElfClass::Elf64
    }

    fn relative_type(&self) -> u32 {
        elf::reloc::R_RISCV_RELATIVE
    }

    fn addend_encoding(&self) -> super::AddendEncoding {
        AddendEncoding::Explicit
    }
}

impl ArchRelocator for Riscv32Relocator {
    fn machine(&self) -> ElfMachine {
        ElfMachine::Riscv
    }

    fn class(&self) -> ElfClass {
        ElfClass::Elf32
    }

    fn relative_type(&self) -> u32 {
        elf::reloc::R_RISCV_RELATIVE
    }

    fn addend_encoding(&self) -> AddendEncoding {
        AddendEncoding::Explicit
    }
}
