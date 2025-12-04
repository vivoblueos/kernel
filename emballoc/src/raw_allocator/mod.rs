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

//! This module provides the raw allocator and its support types.
//!
//! A "raw allocator" is one, that simply gets request for a specific memory
//! size but does not need to worry about alignment.
mod buffer;
mod entry;

use buffer::HEADER_SIZE;
use entry::{Entry, State};

use super::MemoryInfo;
use core::mem::MaybeUninit;

/// An error occurred when calling `free()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FreeError {
    /// There is a double-free detected. An already freed-up-block is freed up
    /// again.
    DoubleFreeDetected,
    /// An invalid pointer was freed up (either a pointer outside of the heap
    /// memory or a pointer to a header).
    AllocationNotFound,
}

/// A raw memory allocator for contiguous slices of bytes without any alignment.
///
/// This allocator is an intermediate one, which does not need to handle the
/// alignment of a [`Layout`](core::alloc::Layout). This abstracts the parts
/// "allocating of memory" and "getting a pointer with proper alignment".
///
/// Note, that the allocated memory is always aligned to `4`.
pub struct RawAllocator<const N: usize> {
    /// The internal buffer abstracting over the raw bytes of the heap.
    buffer: buffer::Buffer<N>,
    max_used: usize,
    used: usize,
}
impl<const N: usize> RawAllocator<N> {
    /// Create a new [`RawAllocator`] with a given heap size.
    ///
    /// # Panics
    /// This function panics if the buffer size is less than `8` (the minimum
    /// useful allocation heap) or if it is not divisible by 4.
    pub const fn new() -> Self {
        debug_assert!(N >= 8, "too small heap memory: minimum size is 8");
        debug_assert!(N % 4 == 0, "memory size has to be divisible by 4");

        let buffer = buffer::Buffer::new();
        Self {
            buffer,
            max_used: 0,
            used: 0,
        }
    }

    /// Allocate a new memory block of size `n`.
    ///
    /// This method is used for general allocation of multiple contiguous bytes.
    /// It searches for the smallest possible free entry and mark it as "used".
    /// As usual with [`RawAllocator`], this does not take alignment in account.
    ///
    /// If the allocation fails, `None` will be returned.
    pub fn alloc(&mut self, n: usize) -> Option<&mut [MaybeUninit<u8>]> {
        self.buffer.ensure_initialization();

        // round up `n` to next multiple of `size_of::<Entry>()`
        let n = (n + HEADER_SIZE - 1) / HEADER_SIZE * HEADER_SIZE;

        let (offset, _) = self
            .buffer
            .entries()
            .map(|offset| (offset, self.buffer[offset]))
            .filter(|(_offset, entry)| entry.state() == State::Free)
            .filter(|(_offset, entry)| entry.size() >= n)
            .min_by_key(|(_offset, entry)| entry.size())?;

        // if the found block is large enough, split it into a used and a free
        self.buffer.mark_as_used(offset, n);
        self.used += n;
        if self.used > self.max_used {
            self.max_used = self.used
        }
        Some(self.buffer.memory_of_mut(offset))
    }

    /// Free a pointer inside a used memory block.
    ///
    /// This method is used to release a memory block allocated with this raw
    /// allocator. If a entry to the given pointer is found, the corresponding
    /// memory block is marked as free. If no entry is found, than an error is
    /// reported (as allocators are not allowed to unwind).
    ///
    /// # Algorithm
    /// Freeing a pointer is done in the following way: all the entries are
    /// scanned linearly. The pointer is compared against each block. If the
    /// pointer points to the memory of an entry, than that entry is selected.
    /// If no such entry is found, than the user tried to free an allocation,
    /// that was not allocated with this allocator (or the allocator messed up
    /// internally). [`FreeError::AllocationNotFound`] is reported.
    ///
    /// The selected block is tested for its state. If it is marked as "used",
    /// than everything is fine. If it is already marked as "free", than
    /// [`FreeError::DoubleFreeDetected`] is returned. If the block following
    /// the just freed up one is also free, the two blocks are concatenated to a
    /// single one (to prevent fragmentation).
    pub fn free(&mut self, ptr: *mut u8) -> Result<(), FreeError> {
        self.buffer.ensure_initialization();

        // find the offset of the entry, which the `ptr` points into
        let offset = self
            .buffer
            .entries()
            .find(|offset| {
                let size = self.buffer[*offset].size();
                let memory = self.buffer.memory_of(*offset);
                let ptr = ptr as *const _;
                let start = memory.as_ptr();
                let end = start.wrapping_add(size);

                start <= ptr && ptr < end
            })
            .ok_or(FreeError::AllocationNotFound)?;

        // check, if the entry is occupied. If it is free, a double free (or a
        // really wrong pointer) was detected, so report an error in that case
        let entry = self.buffer[offset];
        if entry.state() == State::Free {
            return Err(FreeError::DoubleFreeDetected);
        }
        self.used -= self.buffer[offset].size();

        // query the following free memory or `0` if the following entry is used
        let additional_memory = self
            .buffer
            .following_free_entry(offset)
            .map_or(0, |entry| entry.size() + HEADER_SIZE);

        // write the header (entry) to the buffer. If the additional memory is
        // non-zero, then the following entry is simply "ignored" by enlarging
        // the current one
        self.buffer[offset] = Entry::free(entry.size() + additional_memory);
        Ok(())
    }

    pub fn memory_info(&self) -> MemoryInfo {
        MemoryInfo {
            total: N,
            max_used: self.max_used,
            used: self.used,
        }
    }
}
