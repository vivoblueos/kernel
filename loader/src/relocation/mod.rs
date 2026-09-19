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

mod aarch64;
mod arm;
mod riscv;

pub use aarch64::AArch64Relocator;
pub use arm::ArmRelocator;
pub use riscv::{Riscv32Relocator, Riscv64Relocator};

use crate::{
    address::TargetAddress,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult},
    identity::{ElfClass, ElfData, ElfMachine},
    image::RelocationRecord,
    memory::{AllocationOffset, ImageAllocation, ImageLoadTransaction, ImageMemory},
};

#[derive(Clone, Copy)]
pub(crate) enum WordWidth {
    U32,
    U64,
}

impl WordWidth {
    #[inline]
    pub const fn for_elf_class(class: ElfClass) -> Self {
        match class {
            ElfClass::Elf32 => Self::U32,
            ElfClass::Elf64 => Self::U64,
        }
    }

    #[inline]
    pub const fn bytes(self) -> u64 {
        match self {
            Self::U32 => 4,
            Self::U64 => 8,
        }
    }

    #[inline]
    pub const fn maximum(self) -> u64 {
        match self {
            Self::U32 => u32::MAX as u64,
            Self::U64 => u64::MAX,
        }
    }
}

#[derive(Clone, Copy)]
pub enum AddendEncoding {
    Implicit,
    Explicit,
}

/// The four ARM relocation classes handled by the session linker.
///
/// Each arch relocator maps its raw relocation type to one of these; anything
/// unmapped is fail-closed by the session preflight.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelocationKind {
    /// `B + A`: the load-bias plus addend, `symbol_index == 0`.
    Relative,
    /// `S + A`: a resolved symbol value plus addend (data reference).
    Absolute,
    /// `S`: a GOT slot set to the resolved symbol value.
    GlobalData,
    /// `S`: a PLT slot set to the resolved function address.
    JumpSlot,
}

#[derive(Clone, Copy)]
pub(crate) struct TargetWord {
    width: WordWidth,
    endian: ElfData,
}

impl TargetWord {
    #[inline]
    pub const fn new(width: WordWidth, endian: ElfData) -> Self {
        Self { width, endian }
    }

    #[inline]
    pub const fn width(self) -> WordWidth {
        self.width
    }

    pub fn read<M: ImageMemory + ?Sized>(
        self,
        memory: &M,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
    ) -> LoadResult<u64> {
        let mut bytes = [0; 8];
        let len = self.width.bytes() as usize;
        memory.read(allocation, offset, &mut bytes[..len])?;
        Ok(self.decode(bytes))
    }

    fn decode(self, bytes: [u8; 8]) -> u64 {
        let word32 = [bytes[0], bytes[1], bytes[2], bytes[3]];
        match (self.width, self.endian) {
            (WordWidth::U32, ElfData::Little) => u64::from(u32::from_le_bytes(word32)),
            (WordWidth::U32, ElfData::Big) => u64::from(u32::from_be_bytes(word32)),
            (WordWidth::U64, ElfData::Little) => u64::from_le_bytes(bytes),
            (WordWidth::U64, ElfData::Big) => u64::from_be_bytes(bytes),
        }
    }

    pub fn write<M: ImageMemory + ?Sized>(
        self,
        memory: &mut M,
        allocation: &ImageAllocation,
        offset: AllocationOffset,
        value: u64,
    ) -> LoadResult<()> {
        let (bytes, len) = self.encode(offset, value)?;
        memory.write(allocation, offset, &bytes[..len])
    }

    fn encode(self, offset: AllocationOffset, value: u64) -> LoadResult<([u8; 8], usize)> {
        if value > self.width.maximum() {
            return Err(LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::MemoryAccess {
                    allocation_base: TargetAddress::new(0),
                    allocation_len: 0,
                    allocation_align: 0,
                    offset: offset.value(),
                    len: self.width.bytes(),
                },
            ));
        }
        let mut bytes = [0; 8];
        let len = self.width.bytes() as usize;
        match (self.width, self.endian) {
            (WordWidth::U32, ElfData::Little) => {
                bytes[..4].copy_from_slice(&(value as u32).to_le_bytes())
            }
            (WordWidth::U32, ElfData::Big) => {
                bytes[..4].copy_from_slice(&(value as u32).to_be_bytes())
            }
            (WordWidth::U64, ElfData::Little) => bytes.copy_from_slice(&value.to_le_bytes()),
            (WordWidth::U64, ElfData::Big) => bytes.copy_from_slice(&value.to_be_bytes()),
        }
        Ok((bytes, len))
    }

    /// Read through an active image transaction: the transaction supplies
    /// both the memory backend and the owner-bound allocation descriptor.
    pub fn read_via<M: ImageMemory>(
        self,
        transaction: &ImageLoadTransaction<M>,
        offset: AllocationOffset,
    ) -> LoadResult<u64> {
        let mut bytes = [0; 8];
        let len = self.width.bytes() as usize;
        transaction.read(offset, &mut bytes[..len])?;
        Ok(self.decode(bytes))
    }

    /// Write through an active image transaction, marking bytes-modified
    /// before the backend call so a partial write is rolled back correctly.
    pub fn write_via<M: ImageMemory>(
        self,
        transaction: &mut ImageLoadTransaction<M>,
        offset: AllocationOffset,
        value: u64,
    ) -> LoadResult<()> {
        let (bytes, len) = self.encode(offset, value)?;
        transaction.write(offset, &bytes[..len])
    }
}

pub(crate) struct RelocationOperation {
    offset: AllocationOffset,
    value: u64,
    record: RelocationRecord,
}

impl RelocationOperation {
    #[inline]
    pub const fn new(offset: AllocationOffset, value: u64, record: RelocationRecord) -> Self {
        Self {
            offset,
            value,
            record,
        }
    }

    #[inline]
    pub const fn offset(&self) -> AllocationOffset {
        self.offset
    }

    #[inline]
    pub const fn value(&self) -> u64 {
        self.value
    }

    #[inline]
    pub const fn record(&self) -> RelocationRecord {
        self.record
    }
}

pub trait ArchRelocator {
    fn machine(&self) -> ElfMachine;

    fn class(&self) -> ElfClass;

    fn relative_type(&self) -> u32;

    fn addend_encoding(&self) -> AddendEncoding;

    /// Map a raw relocation type to its session engine class, or `None` when
    /// the architecture does not (yet) participate in session-wide relocation.
    /// The ARM32 relocator classifies the four eager-binding relocation types;
    /// everything else remains unsupported.
    fn classify_relocation(&self, _raw_type: u32) -> Option<RelocationKind> {
        None
    }
}

impl<A: ArchRelocator + ?Sized> ArchRelocator for &A {
    fn machine(&self) -> ElfMachine {
        (**self).machine()
    }

    fn class(&self) -> ElfClass {
        (**self).class()
    }

    fn relative_type(&self) -> u32 {
        (**self).relative_type()
    }

    fn addend_encoding(&self) -> AddendEncoding {
        (**self).addend_encoding()
    }

    fn classify_relocation(&self, raw_type: u32) -> Option<RelocationKind> {
        (**self).classify_relocation(raw_type)
    }
}
