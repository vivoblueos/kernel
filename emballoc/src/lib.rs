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

//! Simple allocator for embedded systems
//!
//! This crate provides a single type called [`Allocator`]. This type implements
//! the [`core::alloc::GlobalAlloc`]-trait, which is required to use the
//! [`alloc`-crate][alloc] on `#![no_std]`-targets. The allocator provided in
//! this crate is relatively simple, but reliable: its design is simple, so that
//! errors in the implementation are unlikely. Furthermore the crate is tested
//! rigorously (see below).
//!
//! # Usage
//! The usage is simple: just copy and paste the following code snipped into
//! your binary crate and potentially adjust the number of bytes of the heap
//! (here 4K):
//! ```
//! #[global_allocator]
//! static ALLOCATOR: emballoc::Allocator<4096> = emballoc::Allocator::new();
//!
//! extern crate alloc;
//! ```
//! Afterwards you don't need to interact with the crate or the variable
//! `ALLOCATOR` anymore. Now you can just `use alloc::vec::Vec` or even
//! `use alloc::collections::BTreeMap`, i.e. every fancy collection which is
//! normally provided by the `std`.
//!
//! Note, that the usable dynamic memory is less than the total heap size `N`
//! due to the management of the individual allocations. Each allocation will
//! require a constant memory overhead of _4 bytes_[^note-header-size]. This
//! implies, that more allocations will result in less usable space in the heap.
//! The minimal buffer size is `8`, which would allow exactly one allocation of
//! size up to 4 at a time. Adjust the size as necessary, e.g. by doing a worst
//! case calculation and potentially adding some backup space of 10% (for
//! example).
//!
//! [^note-header-size]: this value is critical for worst-case calculations and
//! therefore part of the stability guarantees of this crate. Changing it will
//! be a breaking change and thus requires a major version bump.
//!
//! The allocator itself is thread-safe, as there is no potentially unsafe
//! [`Cell<T>`]-action done in this crate. Instead it uses the popular [`spin`]
//! crate to use a simple lock on the internal data structures. While this is
//! simple for the implementation, this is not good for performance on
//! multi-threaded systems: you have a global lock for each memory allocation,
//! so only on thread can do a memory allocation at a time. However, this isn't
//! really a problem in embedded systems anyway, as there is only on thread
//! possible without Real Time Operating Systems (RTOS) (which in turn often
//! provide a memory allocator as well, so that one can be used). Therefore this
//! crate is __sound__ and safe to use in multi-threaded contexts, but the
//! performance is not as good as it might be on a lock-free implementation
//! (converting this crate to such a lock free version would be possible, but
//! likely complicate the algorithm and thus is incompatible with the goal to be
//! "simple").
//!
//! A general problem with non-lock-free allocators is the following: it can
//! cause deadlocks even in single-threaded environments if there are interrupts
//! that will _allocate memory_. The interrupt is kind of a second thread, that
//! preempts the first one at any time, even if an allocation is currently in
//! progress. In such a case the interrupt would wait on the lock and never
//! obtain it, since the main program is interrupted and thus cannot release the
//! lock. Therefore it is advised to never use any allocations (or deallocations
//! to the same extend) in an interrupt handler. Performance-wise this shouldn't
//! be done anyway.
//!
//! # Advanced embedded features
//! Note to users with things like `MPU`s, `MMU`s, etc.: your device might
//! support things like memory remapping or memory protection with setting
//! read/write/execution rights. This crate _doesn't use_ those features at all!
//! If that is desired, you should take the address of the buffer and use that
//! along with the known size `N` to protect the heap memory. To users with a
//! fully-working MMU: it is recommended, that you use an allocator, that
//! actually supports paging, etc. This crate might still be helpful, e.g.
//! before setting up the MMU.
//!
//! # Testing
//! As mentioned before: an allocator is a very critical part in the overall
//! system; a misbehaving allocator can break the whole program. Therefore this
//! create is tested extensively[^note-testing]:
//! - there are unit tests and integration tests
//! - the unit tests are run under `miri` to detect undefined behavior, both on
//!   a little-endian and big-endian system
//! - a real-world test using the allocator in the popular `ripgrep` program was
//!   done (see [here][gist_hosted-test])
//!
//! [^note-testing]: The test coverage of different metrics and tools is over
//! 96% (self-set lower limit for this crate). Typically, code coverage tends to
//! vary between coverage measurement kinds (e.g. line/region coverage). One can
//! refer to the latest [codecov.io][codecov] measurement or refer to the more
//! precise measurements obtained by the Rust _instrumented coverage_ feature.
//! Those can be found in the [CI-logs] (see the `coverage` job and there look
//! at "Record testing coverage"). There is a table showing the percentages of
//! different metrics per file.
//!
//! # Implementation
//! This algorithm does a linear scan for free blocks. The basic algorithm is as
//! follows:
//! 1.  We start with an empty buffer.
//!     ```text
//!     xxxx 0000 0000 0000 0000 0000 0000 0000
//!     ^--- ^---------------------------------
//!     FREE size = 28
//!     ```
//!     There is a single entry, which spans all the remaining buffer bytes
//!     (after the entry itself, which is always 4 bytes).
//! 2.  A block of 8 is allocated.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 0000 0000 0000
//!     ^--- ^-------- ^--- ^------------------
//!     USED size = 8  FREE size = 16
//!     ```
//!     Now the only free block (the FREE block of step 1) is split into two.
//!     There is now a used block with a total size of 12 bytes, 4 bytes for the
//!     header and 8 bytes for the content. The remaining buffer space is
//!     occupied by the FREE-element. Note, that the total number of "usable"
//!     space (the memory without the headers) shrunk from 28 to 24 (16 + 8)
//!     bytes, since there is now an additional header.
//! 3.  Another block of 4 is allocated.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 zzzz 0000 0000
//!     ^--- ^-------- ^--- ^--- ^--- ^--------
//!     USED size = 8  USED size FREE size = 8
//!     ```
//!     The same thing as in step 2 happens. Now there are two used blocks and
//!     a single free block with a size of 8.
//! 4.  A request for a block of 16 comes in. There is not enough free memory
//!     for that request. Therefore the allocation fails.
//! 5.  A block of 5 is allocated.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 zzzz 0000 0000
//!     ^--- ^-------- ^--- ^--- ^--- ^-----!!!
//!     USED size = 8  USED size USED size = 8
//!     ```
//!     There is not enough space at the end of the memory buffer, therefore the
//!     current entry is enlarged to fill the remaining space. This "wastes" 3
//!     bytes, but those would not be usable anyway.
//!
//!     To prevent alignment issues, the blocks are always rounded up to a
//!     multiple of 4 as well, which has the same result (this implies, that the
//!     aforementioned special handling of the remaining bytes is not necessary,
//!     care has to be taken to handle 0-sized "free" blocks correctly).
//! 6.  A request for a block of 1 comes in. There is no free memory at all and
//!     hence not enough free memory for that request. Therefore the allocation
//!     fails.
//! 7.  The third allocation (block size 5) is freed.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 zzzz 0000 0000
//!     ^--- ^-------- ^--- ^--- ^--- ^--------
//!     USED size = 8  USED size FREE size = 8
//!     ```
//!     The picture of step 3 is restored.
//! 8.  The first allocation (block size 8) is freed.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 zzzz 0000 0000
//!     ^--- ^-------- ^--- ^--- ^--- ^--------
//!     FREE size = 8  USED size FREE size = 8
//!     ```
//!     Now there are two free blocks and a usable block. Note, that there is
//!     fragmentation, so a request for 12 bytes could not be fulfilled, since
//!     there is no contiguous memory of that size.
//! 9.  Another block of 8 is allocated.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 zzzz 0000 0000
//!     ^--- ^-------- ^--- ^--- ^--- ^--------
//!     USED size = 8  USED size FREE size = 8
//!     ```
//!     Nothing special here, except that the allocator could choose between the
//!     two blocks of 8. Here the first one was chosen (arbitrarily).
//! 10. The second allocation (block size 4) is freed.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 0000 0000 0000
//!     ^--- ^-------- ^--- ^------------------
//!     USED size = 8  FREE size = 16
//!     ```
//!     The block is simply replaced by a FREE block, but there is a caveat: the
//!     two adjacent blocks have to be connected to a single big FREE-block in
//!     order to prevent more fragmentation. They are one continuous block with
//!     a single header.
//!
//!     This connection is easy, since the middle block of step 9 just has to
//!     look for the next header (the position of that block is known by its
//!     size) and check, whether it is free. If so, the new block gets adjusted
//!     to have a size of `self.size + 4 + other.size`. This effectively erases
//!     the right free block.
//! 11. A new block of 8 is allocated. Afterwards the first block is freed.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 0000 0000 0000
//!     ^--- ^-------- ^--- ^-------- ^--- ^---
//!     FREE size = 8  USED size = 8  FREE size
//!     ```
//!     This is just an intermediate step without any issues.
//! 12. The remaining used block is freed.
//!     ```text
//!     xxxx 0000 0000 yyyy 0000 0000 0000 0000
//!     ^--- ^-------- ^--- ^------------------
//!     FREE size = 8  FREE size = 16
//!     ```
//!     Now there are two(!) free blocks, since the concatenation described in
//!     step 10 does only happen to the right side of the freed block. Since the
//!     left block has an unknown size, it is not possible to find the header
//!     (except for linearly scanning the memory from the beginning). Therefore
//!     it is easier to just live with that fragmentation.
//!
//!     Something interesting here is, that one could check for such conditions
//!     from time to time and fix them during that scan. Doing it this way does
//!     not come with a constant time penalty when deallocating. Furthermore it
//!     lets the user decide, whether that feature is necessary or not.
//!
//! [alloc]: https://doc.rust-lang.org/alloc/index.html
//! [gist_hosted-test]: https://gist.github.com/jfrimmel/61943f9879adfbe760a78efa17a0ecaa
//! [`Cell<T>`]: core::cell::Cell
//! [codecov]: https://codecov.io/gh/jfrimmel/emballoc
//! [ci-logs]: https://app.circleci.com/pipelines/github/jfrimmel/emballoc
#![cfg_attr(not(test), no_std)]
#![cfg_attr(compatible_old_toolchain, feature(unsigned_is_multiple_of))] // 1.88
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(clippy::undocumented_unsafe_blocks)]

use raw_allocator::RawAllocator;

use core::{
    alloc::{GlobalAlloc, Layout},
    ptr,
};
use spin::Mutex;

mod raw_allocator;

pub struct MemoryInfo {
    total: usize,
    max_used: usize,
    used: usize,
}

/// The memory allocator for embedded systems.
///
/// This is the core type of this crate: it is an allocator with a predefined
/// heap size. Therefore the heap memory usage is statically limited to an upper
/// value, which also helps to prevent issues with heap/stack-smashes, as the
/// heap is counted to the static memory (e.g. `.data`/`.bss`-sections). Such a
/// smash might still happen though, if the stack pointer grows into the heap,
/// but the heap cannot grow into the stack pointer.
///
/// Its usage is simple: just copy and paste the following in the binary crate
/// you're developing. The memory size of the heap is 4096 bytes (4K) in this
/// example. Adjust that value to your needs.
/// ```no_run
/// #[global_allocator]
/// static ALLOCATOR: emballoc::Allocator<4096> = emballoc::Allocator::new();
/// ```
/// Also please refer to the [crate-level](crate)-documentation for
/// recommendations on the buffer size and general usage.
pub struct Allocator<const N: usize> {
    /// The internal raw allocator.
    ///
    /// The raw allocator handles allocations of contiguous byte slices without
    /// needing to worry about alignment. The raw allocator is protected by a
    /// `spin::Mutex` to make it usable with shared references (requirement of
    /// [`GlobalAlloc`]).
    raw: Mutex<RawAllocator<N>>,
}
impl<const N: usize> Allocator<N> {
    /// Create a new [`Allocator`] with exactly `N` bytes heap space.
    ///
    /// Note, that the usable size is less than the heap size, since there is
    /// some bookkeeping-overhead stored in that area as well. Please see the
    /// [crate-level](crate)-documentation for recommendations on the buffer
    /// size and general usage.
    ///
    /// This function is a `const fn`, therefore you can call it directly when
    /// creating the allocator.
    ///
    /// # Example
    /// Normally one would use a static variable to assign the result of this
    /// function to. When using this, the size is specified in the type and
    /// does not need to be repeated in the call to this function.
    /// ```
    /// static ALLOCATOR: emballoc::Allocator<4096> = emballoc::Allocator::new();
    /// ```
    /// Note: don't use a `const`, as this would freshly instantiate the
    /// allocator every time used and dropping the allocation state.
    ///
    /// If the allocator is used locally, then the size has to be specified like
    /// this:
    /// ```
    /// let allocator = emballoc::Allocator::<64>::new(); // note: smaller size!
    /// ```
    /// Be careful to use a smaller size, since this allocator will be created
    /// on the stack! Therefore it is possible to easily blow up the stack, so
    /// this usage is discouraged and only should be done in special cases.
    ///
    /// # Panics
    /// This function will panic, if the supplied buffer size, i.e. `N`, is less
    /// than `8` or not divisible by `4`.
    /// ```should_panic
    /// emballoc::Allocator::<63>::new(); // not divisible by 4
    /// ```
    /// ```should_panic
    /// emballoc::Allocator::<4>::new(); // less than 8
    /// ```
    #[must_use = "assign the allocator to a static variable and apply the `#[global_allocator]`-attribute to make it the global allocator"]
    #[allow(clippy::new_without_default)] // this could be added, but not now
    pub const fn new() -> Self {
        let raw = Mutex::new(RawAllocator::new());
        Self { raw }
    }

    pub fn memory_info(&self) -> MemoryInfo {
        self.raw.lock().memory_info()
    }

    /// Align a given pointer to the specified alignment.
    ///
    /// # Safety
    /// This function requires `align` to be a power of two and requires the
    /// `ptr` to point to a memory region, that is large enough, so that the
    /// aligned pointer is still in that memory region.
    unsafe fn align_to(ptr: *mut u8, align: usize) -> *mut u8 {
        let addr = ptr as usize;
        let mismatch = addr & (align - 1);
        let offset = if mismatch == 0 { 0 } else { align - mismatch };
        // SAFETY: "in-bound"-requirement is part of the safety-contract of this
        // function, therefore the caller is responsible for it
        unsafe { ptr.add(offset) }
    }
}
// SAFETY: the safety contracts of global allocator is a bit lengthy, but in
// short: the implementation does not panic (at least on purpose, if it would,
// there is a bug) and it actually adheres to the layout requirements (ensured
// by tests).
unsafe impl<const N: usize> GlobalAlloc for Allocator<N> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let align = layout.align();
        // the raw allocator always returns 4-byte-aligned slices, therefore
        // smaller alignments are always fulfilled. Larger alignments are a bit
        // more tricky, since this requires over-allocation and adjusting the
        // pointer accordingly. The over-allocation is rather conservative and
        // uses a worst case estimation, therefore it allocates `align` bytes
        // more, ensuring there is enough memory.
        let size = if align > 4 {
            layout.size() + align
        } else {
            layout.size()
        };

        // allocate a memory block and return the sufficiently aligned pointer
        // into that memory block.
        self.raw
            .lock()
            .alloc(size)
            .map_or(ptr::null_mut(), |memory| {
                // SAFETY: `align` is a power of two as by the contract of
                // `Layout`. Furthermore the memory slice is enlarged (see
                // above), so that the aligned pointer will still be in the same
                // allocation.
                unsafe { Self::align_to(ptr::addr_of_mut!(*memory).cast(), align) }
            })
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        // alignment is irrelevant here, as `RawAllocator::free` can handle any
        // pointer in an entry's memory, so simply forward the pointer. The
        // `free()`-method might detect errors, but those cannot lead to panics
        // (by contract of `GlobalAlloc`). Therefore there are two choices:
        // 1. abort the process
        // 2. ignore the error
        // Since there is no process and there is no stable way to abort the
        // program on `core` the only viable option is option #1: do nothing.
        let _maybe_error = self.raw.lock().free(ptr.cast()).ok();
        // errors are ignored
    }
}

// include the readme in doc-tests. Credits to https://blog.guillaume-gomez.fr/articles/2020-03-07+cfg%28doctest%29+is+stable+and+you+should+use+it
#[cfg(doctest)]
mod extra_doctests {
    /// Helper macro to pass a "dynamic"/included string to the `extern`-block
    macro_rules! doc_check {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }
    // Check the code snippets in the Readme.
    doc_check!(include_str!("../README.md"));
}
