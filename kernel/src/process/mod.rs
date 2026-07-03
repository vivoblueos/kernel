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

//! Process abstraction for AArch64.
//!
//! A Process represents a user-space execution context with its own
//! address space (page table).  Processes are not scheduling entities;
//! Thread is the only schedulable unit.  The Process lifetime is managed
//! by `Arc<Process>` reference counting — there is no state machine
//! (see [[process-no-state-machine]]).
//!
//! Each Thread holds a non-owning raw pointer back to its Process
//! (`Option<NonNull<Process>>`).  When the last `Arc<Process>` is
//! dropped, the address space (page table) is freed and all threads
//! referencing this process observe a null process pointer.

pub mod elf;
#[cfg(target_arch = "aarch64")]
pub(crate) mod first_process;
pub(crate) mod loader;

use crate::{
    arch::aarch64::mmu::{self, PageTableManager},
    mm::{kernel_phys_to_virt, kernel_virt_to_phys},
    types::Arc,
};
use alloc::vec::Vec;
use core::{
    alloc::Layout,
    ptr::NonNull,
    sync::atomic::{fence, Ordering},
};

// Global storage for the first user-space process (AArch64 Phase 3).
// Keeps the Process alive after init_first_process returns.
#[cfg(target_arch = "aarch64")]
pub(crate) static FIRST_PROCESS: crate::sync::SpinLock<Option<Arc<Process>>> =
    crate::sync::SpinLock::new(None);

// ---------------------------------------------------------------------------
// AddressSpace
// ---------------------------------------------------------------------------

/// A process-specific address space, rooted at a L1 page table.
///
/// The `root` is a pointer to the L1 `PageTableManager` that will be
/// installed in TTBR0_EL1 when this process is scheduled.  It is
/// allocated and zeroed on construction and freed (along with all
/// lower-level tables) on drop.
///
/// During Phase 2 the address space is initially empty (no user
/// mappings).  Virtual memory region tracking will be added in a
/// later phase.
pub struct AddressSpace {
    /// Pointer to the L1 page table (root of the translation table walk).
    root: NonNull<PageTableManager>,
    /// Kernel heap allocations backing user-space mappings (ELF segments, stack).
    /// Freed in Drop after the page table tree is released.
    allocs: Vec<(*mut u8, Layout)>,
}

// SAFETY: `AddressSpace` owns the page table exclusively (single-threaded
// access while not scheduled).  `Send` + `Sync` are safe because the owning
// `Process` is protected by `Arc` and the page table is only accessed when
// the process's threads are not concurrently running.
unsafe impl Send for AddressSpace {}
unsafe impl Sync for AddressSpace {}

impl AddressSpace {
    /// Allocate and initialise a new (empty) address space.
    ///
    /// # Errors
    /// Returns `&'static str` if the page-table allocation fails.
    pub fn try_new() -> Result<Self, &'static str> {
        let raw = mmu::alloc_page_table()?;
        Ok(Self {
            root: unsafe { NonNull::new_unchecked(raw) },
            allocs: Vec::new(),
        })
    }

    /// Register a kernel heap allocation that backs a user-space mapping.
    ///
    /// The allocation is freed in `AddressSpace::drop` after the page table
    /// tree has been released.
    pub(crate) fn track_alloc(&mut self, ptr: *mut u8, layout: Layout) {
        self.allocs.push((ptr, layout));
    }

    /// Return the physical address of the root page table.
    ///
    /// Write this value directly to TTBR0_EL1 via `.set(pa as u64)`.
    /// The hardware extracts BADDR from bits [47:1] internally.
    #[inline]
    pub fn root_pa(&self) -> usize {
        let va = self.root.as_ptr() as usize;
        kernel_virt_to_phys(va)
    }

    /// Return a raw pointer to the root page table (virtual address).
    #[inline]
    pub fn root_ptr(&self) -> *mut PageTableManager {
        self.root.as_ptr()
    }
}

impl Drop for AddressSpace {
    fn drop(&mut self) {
        // Recursively free the entire page-table tree.
        // SAFETY: `root` was allocated by `alloc_page_table()` and is
        // not shared — we are the sole owner.
        unsafe {
            mmu::free_page_table(self.root.as_ptr());
        }
        // Free kernel heap allocations that backed user-space mappings.
        // The page table is gone so these pages are no longer reachable from
        // user space; we can safely return them to the allocator.
        for (ptr, layout) in self.allocs.drain(..) {
            unsafe { alloc::alloc::dealloc(ptr, layout) };
        }
    }
}

// ---------------------------------------------------------------------------
// Process
// ---------------------------------------------------------------------------

/// A user-space process.
///
/// Each process has a unique address space and owns zero or more threads.
/// Process lifetime is managed by `Arc<Process>` reference counting.
/// There is no zombie / exited state — when the last reference is dropped
/// the page table is freed automatically.
///
/// # Thread-to-Process back-reference
///
/// Threads hold a non-owning `Option<NonNull<Process>>` pointing to their
/// owning process.  This pointer becomes dangling once the `Process` is
/// dropped, so threads must check `process()` before dereferencing.
/// Because `Process` owns `Arc<Thread>` references, a thread can be
/// confident its process is alive as long as it holds its own `ThreadNode`.
pub struct Process {
    /// The address space (page table root) for this process.
    pub address_space: AddressSpace,
    /// Process ID. The first (init) process has PID 1, following Linux convention.
    /// A full allocator is deferred to Phase 4 (task 3.2).
    pub pid: u32,
    /// Threads belonging to this process.
    ///
    /// In later phases this may become a more sophisticated collection;
    /// for now a simple `Vec` suffices.
    threads: Vec<crate::thread::ThreadNode>,
}

impl Process {
    /// Create a new process with an empty address space.
    ///
    /// # Errors
    /// Returns the `&'static str` error from `AddressSpace::try_new()`
    /// if the page-table allocation fails.
    pub fn try_new(pid: u32) -> Result<Arc<Self>, &'static str> {
        let address_space = AddressSpace::try_new()?;
        Ok(Arc::new(Self {
            address_space,
            pid,
            threads: Vec::new(),
        }))
    }

    /// Register a thread as belonging to a process.
    ///
    /// This pushes the thread into the process's thread list and sets
    /// the thread's back-pointer (see [`crate::thread::Thread::set_process`]).
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` has more than one reference (i.e., the process
    /// has already been shared).
    pub(crate) fn attach_thread(process: &mut Arc<Process>, thread: &crate::thread::ThreadNode) {
        // SAFETY: We hold a unique `Arc<Process>`, so the pointer is alive
        // for the duration of this call.  The raw pointer stored in the
        // thread is valid until the Process is dropped.
        let this = unsafe { NonNull::new_unchecked(Arc::as_ptr(process) as *mut Process) };
        let proc = Arc::get_mut(process)
            .expect("attach_thread: Arc must have unique ownership");
        thread.set_process(this);
        proc.threads.push(thread.clone());
    }

    /// Iterate over the threads attached to this process.
    pub fn threads(&self) -> &[crate::thread::ThreadNode] {
        &self.threads
    }
}

// `Arc<Process>` is sent between cores when the scheduler migrates threads.
unsafe impl Send for Process {}
unsafe impl Sync for Process {}