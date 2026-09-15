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

use crate::error::{ErrorContext, LoadError, LoadErrorKind, LoadResult};

#[non_exhaustive]
#[derive(PartialEq, PartialOrd, Clone, Copy, Debug, Eq, Ord)]
pub struct TargetAddress(u64);

impl TargetAddress {
    #[inline]
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    #[inline]
    pub const fn get(self) -> u64 {
        self.0
    }

    pub fn checked_add(self, value: u64) -> LoadResult<Self> {
        self.0.checked_add(value).map(Self).ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::TargetRange {
                    start: self,
                    len: value,
                    align: 0,
                },
            )
        })
    }

    pub fn checked_sub(self, other: Self) -> LoadResult<u64> {
        self.0.checked_sub(other.0).ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::TargetRange {
                    start: other,
                    len: self.0,
                    align: 0,
                },
            )
        })
    }

    pub fn align_down(self, align: u64) -> LoadResult<Self> {
        if !align.is_power_of_two() {
            return Err(LoadError::new(
                LoadErrorKind::InvalidAlignment,
                ErrorContext::TargetRange {
                    start: self,
                    len: 0,
                    align,
                },
            ));
        }
        Ok(Self(self.0 & !(align - 1)))
    }

    pub fn align_up(self, align: u64) -> LoadResult<Self> {
        if !align.is_power_of_two() {
            return Err(LoadError::new(
                LoadErrorKind::InvalidAlignment,
                ErrorContext::TargetRange {
                    start: self,
                    len: 0,
                    align,
                },
            ));
        }
        let mask = align - 1;
        Ok(Self(self.checked_add(mask)?.0 & !mask))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TargetRange {
    start: TargetAddress,
    len: u64,
}

impl TargetRange {
    #[inline]
    pub const fn new(start: TargetAddress, len: u64) -> Self {
        Self { start, len }
    }

    #[inline]
    pub const fn start(self) -> TargetAddress {
        self.start
    }

    #[inline]
    pub const fn len(self) -> u64 {
        self.len
    }

    #[inline]
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    pub fn end(self) -> LoadResult<TargetAddress> {
        self.start.checked_add(self.len)
    }

    pub fn contains_span(self, start: TargetAddress, len: u64) -> bool {
        let Ok(self_end) = self.end() else {
            return false;
        };
        let Ok(span_end) = start.checked_add(len) else {
            return false;
        };
        start >= self.start && span_end <= self_end
    }

    pub fn overlaps(self, other: Self) -> bool {
        if self.is_empty() || other.is_empty() {
            return false;
        }
        let (Ok(self_end), Ok(other_end)) = (self.end(), other.end()) else {
            return false;
        };
        self.start < other_end && other.start < self_end
    }
}

#[derive(Clone, Copy)]
pub struct FileRange {
    offset: u64,
    len: u64,
}

impl FileRange {
    #[inline]
    pub const fn new(offset: u64, len: u64) -> Self {
        Self { offset, len }
    }

    #[inline]
    pub const fn offset(self) -> u64 {
        self.offset
    }

    #[inline]
    pub const fn len(self) -> u64 {
        self.len
    }

    #[inline]
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    pub fn end(self) -> LoadResult<u64> {
        self.offset.checked_add(self.len).ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::IntegerOverflow,
                ErrorContext::FileRange {
                    offset: self.offset,
                    len: self.len,
                    file_len: 0,
                },
            )
        })
    }

    pub fn validate(self, file_len: u64) -> LoadResult<()> {
        if self.end()? <= file_len {
            return Ok(());
        }
        Err(LoadError::new(
            LoadErrorKind::OutOfBounds,
            ErrorContext::FileRange {
                offset: self.offset,
                len: self.len,
                file_len,
            },
        ))
    }
}
