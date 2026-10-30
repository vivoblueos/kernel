// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

//! This module exposes the ubiquitous [`Entry`] type and its helper [`State`].
#[cfg(test)]
use core::fmt::{self, Debug, Formatter};

/// Helper for showing, whether a block is used or freed.
///
/// This primarily exists to be able to match on the block state and to work
/// ergonomically with it.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum State {
    /// The entry is marked as "used".
    ///
    /// The memory after the header is assumed to contain used data and must not
    /// be re-used for other allocations.
    Free,
    /// The entry is marked as "free".
    ///
    /// The memory after the header is assumed to be free and thus can be used
    /// for a new allocation.
    Used,
}

/// An (un)allocated block.
///
/// Such a block is either used or free and contains a block size. It is a
/// compact version of the following `enum`:
/// ```
/// # use core::mem;
/// enum NaiveEntry {
///     Used(u32),
///     Free(u32),
/// }
///
/// // mem::size_of::<Entry>() is not possible in doc-tests, since the struct is not exposed
/// assert!(mem::size_of::<NaiveEntry>() > mem::size_of::<u32>());
/// ```
/// This struct is used heavily in the allocator and thus has to be optimized.
/// It is used as a header for blocks of allocated or unallocated memory inside
/// the heap buffer. Entries are written directly into the buffer, therefore
/// their layout is important.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Entry(u32);
impl Entry {
    /// Create a new free [`Entry`] with the given size.
    ///
    /// Note, that the `size` is the number of bytes of the payload, i.e. the
    /// size after the `Entry` itself. This is the same value as returned by
    /// [`size()`](Entry::size()).
    pub const fn free(size: usize) -> Self {
        debug_assert!(size <= 0x7FFF_FFFF);
        #[allow(clippy::cast_possible_truncation)] // asserted above
        Self((size << 1) as _)
    }

    /// Create a new occupied/used [`Entry`] with the given size.
    ///
    /// Note, that the `size` is the number of bytes of the payload, i.e. the
    /// size after the `Entry` itself. This is the same value as returned by
    /// [`size()`](Entry::size()).
    pub const fn used(size: usize) -> Self {
        debug_assert!(size <= 0x7FFF_FFFF);
        #[allow(clippy::cast_possible_truncation)] // asserted above
        Self((size << 1 | 1) as _)
    }

    /// Query the allocation state of this block.
    pub const fn state(self) -> State {
        if self.0 & 1 == 0 {
            State::Free
        } else {
            State::Used
        }
    }

    /// Query the size of the block.
    ///
    /// This is the size of the usable memory, i.e. the header size is not
    /// included.
    pub const fn size(self) -> usize {
        let size = self.0 >> 1;
        size as _
    }

    /// Query the raw bytes of this entry in native endian order.
    pub const fn as_raw(self) -> [u8; 4] {
        self.0.to_ne_bytes()
    }
}
#[cfg(test)]
impl Debug for Entry {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Entry")
            .field("state", &self.state())
            .field("size", &self.size())
            .finish()
    }
}
