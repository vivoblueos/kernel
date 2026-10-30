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

//! ELF wire structures and bounds-checked integer decoding.
//! Image admission policy is implemented in `image`.

mod header;
mod program_header;

use crate::{
    error::{ErrorContext, LoadErrorKind},
    profile::ElfData,
    LoadError, LoadResult,
};
use goblin::{elf32, elf64};

pub(crate) use header::ElfHeaderInfo;
pub(crate) use program_header::ProgramHeaderInfo;

pub(crate) const ELF_IDENT_SIZE: usize = 16;
pub(crate) const ELF32_HEADER_SIZE: usize = elf32::header::SIZEOF_EHDR;
pub(crate) const ELF64_HEADER_SIZE: usize = elf64::header::SIZEOF_EHDR;
pub(crate) const ELF32_PROGRAM_HEADER_SIZE: usize = elf32::program_header::SIZEOF_PHDR;
pub(crate) const ELF64_PROGRAM_HEADER_SIZE: usize = elf64::program_header::SIZEOF_PHDR;

pub(crate) fn read_u16(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u16> {
    let raw = read_array::<2>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u16::from_le_bytes(raw),
        ElfData::Big => u16::from_be_bytes(raw),
    })
}

pub(crate) fn read_u32(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u32> {
    let raw = read_array::<4>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u32::from_le_bytes(raw),
        ElfData::Big => u32::from_be_bytes(raw),
    })
}

pub(crate) fn read_u64(bytes: &[u8], offset: usize, endian: ElfData) -> LoadResult<u64> {
    let raw = read_array::<8>(bytes, offset)?;
    Ok(match endian {
        ElfData::Little => u64::from_le_bytes(raw),
        ElfData::Big => u64::from_be_bytes(raw),
    })
}

fn read_array<const N: usize>(bytes: &[u8], offset: usize) -> LoadResult<[u8; N]> {
    let end = offset.checked_add(N).ok_or_else(|| {
        LoadError::new(
            LoadErrorKind::IntegerOverflow,
            ErrorContext::FileRange {
                offset: offset as u64,
                len: N as u64,
                file_len: bytes.len() as u64,
            },
        )
    })?;
    let src = bytes.get(offset..end).ok_or_else(|| {
        LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::FileRange {
                offset: offset as u64,
                len: N as u64,
                file_len: bytes.len() as u64,
            },
        )
    })?;
    let mut raw = [0; N];
    raw.copy_from_slice(src);
    Ok(raw)
}
