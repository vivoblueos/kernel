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
    address::{FileRange, TargetAddress},
    MemoryPermissions,
};

pub(crate) struct LoadSegmentInfo {
    index: u16,
    file_range: FileRange,
    vaddr: TargetAddress,
    memory_size: u64,
    align: u64,
    permissions: MemoryPermissions,
}

impl LoadSegmentInfo {
    #[inline]
    pub const fn new(
        index: u16,
        file_range: FileRange,
        vaddr: TargetAddress,
        memory_size: u64,
        align: u64,
        permissions: MemoryPermissions,
    ) -> Self {
        Self {
            index,
            file_range,
            vaddr,
            memory_size,
            align,
            permissions,
        }
    }

    #[inline]
    pub const fn index(&self) -> u16 {
        self.index
    }

    #[inline]
    pub const fn file_range(&self) -> FileRange {
        self.file_range
    }

    #[inline]
    pub const fn vaddr(&self) -> TargetAddress {
        self.vaddr
    }

    #[inline]
    pub const fn memory_size(&self) -> u64 {
        self.memory_size
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        self.align
    }

    #[inline]
    pub const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }
}

#[derive(Clone)]
pub(crate) struct DynamicSegmentInfo {
    file_range: FileRange,
    vaddr: TargetAddress,
    memory_size: u64,
}

impl DynamicSegmentInfo {
    #[inline]
    pub const fn new(file_range: FileRange, vaddr: TargetAddress, memory_size: u64) -> Self {
        Self {
            file_range,
            vaddr,
            memory_size,
        }
    }

    #[inline]
    pub const fn file_range(&self) -> FileRange {
        self.file_range
    }

    #[inline]
    pub const fn vaddr(&self) -> TargetAddress {
        self.vaddr
    }

    #[inline]
    pub const fn memory_size(&self) -> u64 {
        self.memory_size
    }
}
