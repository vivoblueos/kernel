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

use crate::identity::{ElfClass, ElfData, ElfMachine, ElfType};

pub(crate) struct ElfHeaderInfo {
    class: ElfClass,
    endian: ElfData,
    r#type: ElfType,
    machine: ElfMachine,
    entry: u64,
    program_header_offset: u64,
    program_header_entry_size: u16,
    program_header_count: u16,
    flags: u32,
}

impl ElfHeaderInfo {
    #[inline]
    pub const fn new(
        class: ElfClass,
        endian: ElfData,
        r#type: ElfType,
        machine: ElfMachine,
        entry: u64,
        program_header_offset: u64,
        program_header_entry_size: u16,
        program_header_count: u16,
        flags: u32,
    ) -> Self {
        Self {
            class,
            endian,
            r#type,
            machine,
            entry,
            program_header_offset,
            program_header_entry_size,
            program_header_count,
            flags,
        }
    }

    #[inline]
    pub const fn class(&self) -> ElfClass {
        self.class
    }

    #[inline]
    pub const fn endian(&self) -> ElfData {
        self.endian
    }

    #[inline]
    pub const fn r#type(&self) -> ElfType {
        self.r#type
    }

    #[inline]
    pub const fn machine(&self) -> ElfMachine {
        self.machine
    }

    #[inline]
    pub const fn entry(&self) -> u64 {
        self.entry
    }

    #[inline]
    pub const fn program_header_offset(&self) -> u64 {
        self.program_header_offset
    }

    #[inline]
    pub const fn program_header_entry_size(&self) -> u16 {
        self.program_header_entry_size
    }

    #[inline]
    pub const fn program_header_count(&self) -> u16 {
        self.program_header_count
    }

    #[inline]
    pub const fn flags(&self) -> u32 {
        self.flags
    }
}
