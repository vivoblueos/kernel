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

use crate::{
    address::TargetAddress,
    error::{LoadResult, LoadStage},
    identity::{ElfClass, ElfData},
    image::{read_u32, read_u64},
};

pub(crate) struct ProgramHeaderInfo {
    r#type: u32,
    flags: u32,
    file_offset: u64,
    vaddr: TargetAddress,
    file_size: u64,
    memory_size: u64,
    align: u64,
}

impl ProgramHeaderInfo {
    #[inline]
    pub const fn r#type(&self) -> u32 {
        self.r#type
    }

    #[inline]
    pub const fn flags(&self) -> u32 {
        self.flags
    }

    #[inline]
    pub const fn file_offset(&self) -> u64 {
        self.file_offset
    }

    #[inline]
    pub const fn vaddr(&self) -> TargetAddress {
        self.vaddr
    }

    #[inline]
    pub const fn file_size(&self) -> u64 {
        self.file_size
    }

    #[inline]
    pub const fn memory_size(&self) -> u64 {
        self.memory_size
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        self.align
    }

    pub fn decode(bytes: &[u8], class: ElfClass, endian: ElfData) -> LoadResult<Self> {
        Ok(match class {
            ElfClass::Elf32 => Self {
                r#type: read_u32(bytes, 0, endian)?,
                file_offset: u64::from(read_u32(bytes, 4, endian)?),
                vaddr: TargetAddress::new(u64::from(read_u32(bytes, 8, endian)?)),
                file_size: u64::from(read_u32(bytes, 16, endian)?),
                memory_size: u64::from(read_u32(bytes, 20, endian)?),
                flags: read_u32(bytes, 24, endian)?,
                align: u64::from(read_u32(bytes, 28, endian)?),
            },
            ElfClass::Elf64 => Self {
                r#type: read_u32(bytes, 0, endian)?,
                flags: read_u32(bytes, 4, endian)?,
                file_offset: read_u64(bytes, 8, endian)?,
                vaddr: TargetAddress::new(read_u64(bytes, 16, endian)?),
                file_size: read_u64(bytes, 32, endian)?,
                memory_size: read_u64(bytes, 40, endian)?,
                align: read_u64(bytes, 48, endian)?,
            },
        })
    }
}
