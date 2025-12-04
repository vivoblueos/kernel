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

//! Module providing the [`Buffer`] abstraction and its related types.
//!
//! This module tries to encapsulate all the low-level details on working with
//! uninitialized heap memory, alignment into that buffer and reading/writing
//! [`Entry`]s.
use super::entry::{Entry, State};

use core::mem::{self, MaybeUninit};

/// The size of a single block header.
pub const HEADER_SIZE: usize = mem::size_of::<Entry>();

/// An offset into the [`Buffer`], that is validated and known to be safe.
///
/// See [`EntryIter`] for details on the idea and necessity of this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidatedOffset(usize);

/// The buffer memory backing the heap.
#[repr(align(4))]
pub struct Buffer<const N: usize>([MaybeUninit<u8>; N]);
impl<const N: usize> Buffer<N> {
    /// Create a new buffer.
    ///
    /// This buffer will be uninitialized except for the first few bytes: the
    /// firs `HEADER_SIZE` bytes are initialized to zero. The caller must
    /// subsequently call [`Buffer::ensure_initialization()`] to initialize the
    /// first bytes as the header. This header is a free [`Entry`] with the size
    /// of the remaining buffer.
    ///
    /// # Panics
    /// This function panics if the buffer is less than 4 bytes in size, i.e. if
    /// `N < 4`.
    pub const fn new() -> Self {
        debug_assert!(N >= HEADER_SIZE, "buffer too small, use N >= 4");
        debug_assert!(N % HEADER_SIZE == 0, "memory size has to be divisible by 4");

        // initialize the header bytes to zero to make sure, that we can check
        // against zero later without undefined behavior.
        let mut buffer = [MaybeUninit::uninit(); N];
        buffer[0] = MaybeUninit::new(0x00);
        buffer[1] = MaybeUninit::new(0x00);
        buffer[2] = MaybeUninit::new(0x00);
        buffer[3] = MaybeUninit::new(0x00);
        Self(buffer)
    }

    /// Ensure, that the buffer is initialized.
    ///
    /// This separate step is necessary to make sure, that the buffer is not
    /// initialized with non-zero data in the binary (i.e when calling `new()`).
    pub fn ensure_initialization(&mut self) {
        let buffer = &mut self.0;
        let not_yet_initialized = buffer
            .iter_mut()
            .take(HEADER_SIZE)
            // SAFETY: the bytes of the first entry are initialized in `new()`
            .map(|byte| unsafe { byte.assume_init() })
            .all(|byte| byte == 0x00);

        if not_yet_initialized {
            let remaining_size = N - HEADER_SIZE;
            let initial_entry = Entry::free(remaining_size).as_raw();

            buffer[0] = MaybeUninit::new(initial_entry[0]);
            buffer[1] = MaybeUninit::new(initial_entry[1]);
            buffer[2] = MaybeUninit::new(initial_entry[2]);
            buffer[3] = MaybeUninit::new(initial_entry[3]);
        }
    }

    /// Obtain a reference to an [`Entry`] inside of the buffer.
    ///
    /// The returned memory will point inside the buffer itself and thus
    /// modifying the reference will modify the buffer contents. This is a safe
    /// operation, since the calling requirements (see below) are checked at
    /// runtime. For safety-reasons this function does not return the [`Entry`]
    /// directly, but instead uses a [`MaybeUninit<Entry>`] instead. Without
    /// this, the function would be unsafe, since the caller would need to
    /// guarantee, that the memory read is actually filled with a valid and
    /// initialized `Entry`. By using the `MaybeUninit`-variant, the caller has
    /// to use the `unsafe`-block when actually reading and assuming, that it is
    /// initialized.
    ///
    /// # Panics
    /// This function panics if the offset is not a multiple of 4 or the offset
    /// plus the 4 bytes after it would read past the end of the buffer.
    fn at(&self, offset: usize) -> &MaybeUninit<Entry> {
        debug_assert!(offset % mem::align_of::<Entry>() == 0);
        debug_assert!(offset + HEADER_SIZE <= self.0.len());

        // SAFETY: this operation is unsafe for multiple reasons: the alignment
        // has to be satisfied and the entry read must be in bound of the buffer
        // memory.
        // 1. the bounds of the memory is checked by the assert above: the
        //    current offset plus the number of bytes read for an `Entry` is
        //    inside the buffer. Therefore this safety requirement is always
        //    fulfilled.
        // 2. the proper alignment is ensured by first checking, whether the
        //    offset is a multiple of the alignment of `Entry`. This makes sure,
        //    that we are aligned within the buffer. Another important aspect is
        //    that the buffer itself is aligned. This is achieved using a
        //    `#[repr(align(4))]`-attribute on the buffer itself. Therefore the
        //    alignment safety requirement is fulfilled as well.
        //
        // Note, that the memory, that is pointed to, might not contain a valid
        // `Entry`. This is fine, since the function returns a `MaybeUninit`
        // version of an `Entry`. Therefore the caller has to ensure, that the
        // thing written or read is valid.
        unsafe {
            let memory = &self.0[offset..offset + 4];
            let memory = memory.as_ptr();
            #[allow(clippy::cast_ptr_alignment)] // alignment is asserted above
            &*(memory
                .cast::<[MaybeUninit<u8>; 4]>()
                .cast::<MaybeUninit<Entry>>())
        }
    }

    /// Obtain a mutable reference to an [`Entry`] inside of the buffer.
    ///
    /// Please see [`at()`](Self::at) for details.
    ///
    /// # Panics
    /// This function panics if the offset is not a multiple of 4 or the offset
    /// plus the 4 bytes after it would read past the end of the buffer.
    fn at_mut(&mut self, offset: usize) -> &mut MaybeUninit<Entry> {
        debug_assert!(offset % mem::align_of::<Entry>() == 0);
        debug_assert!(offset + HEADER_SIZE <= self.0.len());

        // SAFETY: same as `at()`
        unsafe {
            let memory = &mut self.0[offset..offset + 4];
            let memory = memory.as_mut_ptr();
            #[allow(clippy::cast_ptr_alignment)] // alignment is asserted above
            &mut *(memory
                .cast::<[MaybeUninit<u8>; 4]>()
                .cast::<MaybeUninit<Entry>>())
        }
    }

    /// Iterate over all entries and obtain the [`ValidatedOffset`]s.
    pub const fn entries(&self) -> EntryIter<N> {
        EntryIter::new(self)
    }

    /// Request the memory of an entry at a [`ValidatedOffset`].
    ///
    /// This operation is safe, since the offset is validated. It returns the
    /// slice of the memory of the given entry.
    pub fn memory_of(&self, offset: ValidatedOffset) -> &[MaybeUninit<u8>] {
        let size = self[offset].size();

        let offset = offset.0 + HEADER_SIZE;
        &self.0[offset..offset + size]
    }

    /// Request the mutable memory of an entry at a [`ValidatedOffset`].
    ///
    /// This operation is safe, since the offset is validated. It returns the
    /// slice of the memory of the given entry.
    pub fn memory_of_mut(&mut self, offset: ValidatedOffset) -> &mut [MaybeUninit<u8>] {
        let size = self[offset].size();

        let offset = offset.0 + HEADER_SIZE;
        &mut self.0[offset..offset + size]
    }

    /// Query the following free entry, if there is such an entry.
    ///
    /// This function takes a [`ValidatedOffset`] of one entry and tries to
    /// obtain the entry after it. If there is no entry after it (because the
    /// given one is the last in the buffer) or if the entry following it is a
    /// used one, then `None` is returned.
    #[allow(clippy::needless_pass_by_ref_mut)] // this is a "mutable" operation
    pub fn following_free_entry(&mut self, offset: ValidatedOffset) -> Option<Entry> {
        let iter_starting_at_offset = EntryIter {
            buffer: self,
            offset: offset.0,
        };

        iter_starting_at_offset
            .map(|offset| self[offset])
            .nth(1)
            .filter(|entry| entry.state() == State::Free)
    }

    /// Mark the given `Entry` as used and try to split it up.
    ///
    /// This function will mark the `Entry` at the given offset as "used". The
    /// block therefore will be marked as allocated. If the block at the offset
    /// is large enough, it will be split into the used part and a new free
    /// `Entry`, which holds the remaining memory (except for the necessary
    /// header space). If the entry is not large enough for splitting, than the
    /// entry is simply converted to an used entry.
    pub fn mark_as_used(&mut self, offset: ValidatedOffset, size: usize) {
        let old_size = self[offset].size();
        debug_assert!(old_size >= size);

        self[offset] = Entry::used(size);
        if let Some(remaining_size) = (old_size - size).checked_sub(HEADER_SIZE) {
            self.at_mut(offset.0 + size + HEADER_SIZE)
                .write(Entry::free(remaining_size));
        }
    }
}
impl<const N: usize> core::ops::Index<ValidatedOffset> for Buffer<N> {
    type Output = Entry;

    fn index(&self, index: ValidatedOffset) -> &Self::Output {
        // SAFETY: the `ValidatedOffset` marks the read valid (safety invariant
        // of that type)
        unsafe { self.at(index.0).assume_init_ref() }
    }
}
impl<const N: usize> core::ops::IndexMut<ValidatedOffset> for Buffer<N> {
    fn index_mut(&mut self, index: ValidatedOffset) -> &mut Self::Output {
        // SAFETY: the `ValidatedOffset` marks the read valid (safety invariant
        // of that type)
        unsafe { self.at_mut(index.0).assume_init_mut() }
    }
}

/// An iterator over the allocation entries in a [`Buffer`].
///
/// This iterator does not yield [`Entry`]s directly but rather yields so-called
/// [`ValidatedOffset`]s. Those can be used to access the entries in a mutable
/// and immutable way via indexing (`buffer[offset]`). This design was chosen,
/// since the naive way of an `EntryIter` and `EntryIterMut`, which yield
/// `&Entry` and `&mut Entry` result in many borrowing issues.
///
/// One could make this iterator yield the offsets as plain `usize`s, but the
/// newtype is a better solution: it allows to know, that the offset comes from
/// a known place (this iterator, which knows, that there is an entry at that
/// offset. If there were none, the iteration wouldn't be possible) and thus
/// the indexing can become safe. This builds on the assumption, that nobody
/// constructs an invalid `ValidatedOffset`.
pub struct EntryIter<'buffer, const N: usize> {
    /// The memory to iterate over.
    ///
    /// This must be in a valid state (starting with an entry at offset `0` and
    /// headers after all entries until the end of the buffer) in order for the
    /// iteration to succeed.
    buffer: &'buffer Buffer<N>,
    /// The current offset into the buffer.
    offset: usize,
}
impl<'buffer, const N: usize> EntryIter<'buffer, N> {
    /// Create an entry iterator over the given [`Buffer`].
    const fn new(buffer: &'buffer Buffer<N>) -> Self {
        Self { buffer, offset: 0 }
    }
}
impl<'buffer, const N: usize> Iterator for EntryIter<'buffer, N> {
    type Item = ValidatedOffset;

    fn next(&mut self) -> Option<Self::Item> {
        (self.offset + HEADER_SIZE < N).then(|| {
            let offset = self.offset;
            // SAFETY: the buffer invariant (valid entries) have to be upheld
            let entry = unsafe { self.buffer.at(offset).assume_init_ref() };
            self.offset += entry.size() + HEADER_SIZE;
            ValidatedOffset(offset)
        })
    }
}
