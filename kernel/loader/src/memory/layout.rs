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

//! Image address placement, logical permissions and loadable byte ranges.

use alloc::vec::Vec;

use super::{TargetAddress, TargetRange};
use crate::{
    error::{ErrorContext, LoadErrorKind},
    LoadError, LoadResult,
};

/// Logical R/W/X combinations shared by loader policies and memory backends.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoryPermissions(u8);

impl MemoryPermissions {
    pub const NONE: Self = Self(0);
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXECUTE: Self = Self(1 << 2);

    pub const fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }

    pub(crate) const fn bits(self) -> u8 {
        self.0
    }

    pub const fn contains(self, requested: Self) -> bool {
        self.0 & requested.0 == requested.0
    }
}

/// Target address placement required by an image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement {
    /// Any suitably aligned address (ET_DYN images).
    Anywhere,
    /// Exactly this virtual range (ET_EXEC images).
    Fixed(TargetRange),
}

/// Byte offset from the target base of one image allocation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
pub struct AllocationOffset(u64);

impl AllocationOffset {
    #[inline]
    pub const fn new(offset: u64) -> Self {
        Self(offset)
    }

    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }

    pub fn checked_add(self, value: u64) -> LoadResult<Self> {
        let offset = self.0.checked_add(value).ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::MemoryAccess {
                    allocation_base: TargetAddress::new(0),
                    allocation_len: 0,
                    allocation_align: 0,
                    offset: self.0,
                    len: value,
                },
            )
        })?;
        Ok(Self::new(offset))
    }
}

/// A nonempty PT_LOAD memory range, relative to the image reservation base.
///
/// Permissions describe the segment's intended execution state. The backend
/// must still provide loader reads and writes until final protection is applied.
/// File offsets and initialized sizes remain the loader's responsibility.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SegmentLayout {
    allocation_offset: AllocationOffset,
    memory_size: u64,
    permissions: MemoryPermissions,
}

impl SegmentLayout {
    pub const fn new(
        allocation_offset: AllocationOffset,
        memory_size: u64,
        permissions: MemoryPermissions,
    ) -> Self {
        Self {
            allocation_offset,
            memory_size,
            permissions,
        }
    }

    /// Byte offset from the image allocation's target base.
    pub const fn allocation_offset(&self) -> AllocationOffset {
        self.allocation_offset
    }

    pub const fn memory_size(&self) -> u64 {
        self.memory_size
    }

    pub const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }
}

/// Validated layout of one image, independent of its physical backing.
///
/// The complete span is reserved once, so every segment uses the same load
/// bias. Segments are sorted, nonempty, disjoint byte ranges inside that span.
/// Gaps need not have physical backing. A paging backend must prepare shared
/// boundary pages only once and reject unsupported page permission conflicts.
/// This value owns layout metadata only; cloning it does not create another
/// reservation or duplicate the unique allocation handle.
#[derive(Clone, Debug)]
pub struct ImageLayout {
    placement: Placement,
    size: u64,
    align: u64,
    segments: Vec<SegmentLayout>,
}

impl ImageLayout {
    pub fn new(
        placement: Placement,
        size: u64,
        align: u64,
        segments: Vec<SegmentLayout>,
    ) -> LoadResult<Self> {
        let base = match placement {
            Placement::Anywhere => TargetAddress::new(0),
            Placement::Fixed(range) => range.start(),
        };
        let error = |kind| {
            LoadError::new(
                kind,
                ErrorContext::TargetRange {
                    start: base,
                    len: size,
                    align,
                },
            )
        };
        if !align.is_power_of_two() {
            return Err(error(LoadErrorKind::InvalidAlignment));
        }
        if size == 0 || segments.is_empty() {
            return Err(error(LoadErrorKind::IncorrectLayout));
        }
        if let Placement::Fixed(range) = placement {
            if range.len() != size || base.get().checked_rem(align) != Some(0) {
                return Err(error(LoadErrorKind::IncorrectLayout));
            }
            range.end()?;
        }
        let mut previous_end = 0;
        for segment in &segments {
            let start = segment.allocation_offset().value();
            let end = start
                .checked_add(segment.memory_size())
                .ok_or_else(|| error(LoadErrorKind::IntegerOverflow))?;
            if segment.memory_size() == 0 || start < previous_end {
                return Err(error(LoadErrorKind::IncorrectLayout));
            }
            if end > size {
                return Err(error(LoadErrorKind::OutOfBounds));
            }
            previous_end = end;
        }
        Ok(Self {
            placement,
            size,
            align,
            segments,
        })
    }

    pub const fn placement(&self) -> Placement {
        self.placement
    }

    pub const fn size(&self) -> u64 {
        self.size
    }

    pub const fn align(&self) -> u64 {
        self.align
    }

    pub fn segments(&self) -> &[SegmentLayout] {
        &self.segments
    }
}
