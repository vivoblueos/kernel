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

//! First user-space process bootstrap.
//!
//! This module implements the end-to-end flow for launching the first
//! user-space process on AArch64:
//!
//! 1. Create a [`Process`] with a dedicated [`AddressSpace`].
//! 2. Load a statically-linked PIE ELF binary into that address space
//!    using [`PageTableAllocator`] + the local ELF loader.
//! 3. Allocate an 8 KB user stack.
//! 4. Create a kernel-mode [`Thread`] whose [`Context`] is initialised
//!    for EL0 entry (SPSR_EL1 = EL0t, ELR_EL1 = entry point).
//! 5. Queue the thread on the BSP core.
//!
//! # Constraints (Phase 3)
//!
//! * Only **ET_DYN** (PIE) ELFs are supported.
//! * The user stack is 8 KB, located at `USER_STACK_BASE`.
//! * Dynamic linking (INTERP) is detected but produces only a warning.
//! * The ELF binary is embedded via `include_bytes!`.

use crate::{
    arch::Context,
    process::{elf::MemoryAllocator, elf::PageTableAllocator, loader, AddressSpace, Process},
    scheduler,
    thread::{self, Entry, Stack, Thread, ThreadNode},
    types::{Arc, ThreadPriority},
};
use alloc::vec::Vec;
use core::ptr::NonNull;

// ---------------------------------------------------------------------------
// Embedded ELF binary
// ---------------------------------------------------------------------------

/// The embedded first-process ELF binary, injected at build time.
///
/// The path is set via GN `rustenv` (`FIRST_ELF_RS_PATH`), pointing to a
/// generated `.rs` file produced by `gen_bytes.py` from the `first_elf` target.
include!(concat!(env!("FIRST_ELF_RS_PATH")));

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Entry point returned by [`load_user_elf`].
pub(crate) struct LoadedElf {
    /// Virtual address of the entry point (ELR_EL1 target).
    pub entry: usize,
    /// Top of the user stack (SP_EL0 initial value).
    pub stack_top: usize,
}

/// Load an ELF binary into a process address space and allocate the user stack.
///
/// Returns the entry point and stack top on success.
///
/// # Parameters
///
/// * `elf_data` — raw ELF binary bytes.
/// * `address_space` — the target address space to map into.
///
/// # Errors
///
/// Returns `&'static str` if the ELF is malformed, the loader rejects it, or
/// memory allocation / mapping fails.
pub(crate) fn load_user_elf(
    elf_data: &[u8],
    address_space: &mut AddressSpace,
) -> Result<LoadedElf, &'static str> {
    // 1. Create PageTableAllocator for this address space.
    let mut allocator = PageTableAllocator::new(address_space);

    // 2. Parse and load the ELF via the local loader.
    let binary = loader::Elf::parse(elf_data)
        .map_err(|_| "ELF parse failed")?;
    loader::load_elf(elf_data, &mut allocator)?;

    // 3. Zero BSS segments (p_memsz > p_filesz).
    loader::zero_bss_segments(&binary, &mut allocator)?;

    // 4. Check for INTERP segment (warn, but proceed for static PIE).
    loader::check_interp(&binary);

    // 5. Allocate user stack.
    let stack_top = super::elf::allocate_user_stack(address_space)?;

    // 6. Resolve the real entry point.
    let entry = allocator.real_entry()?;

    Ok(LoadedElf { entry, stack_top })
}

/// Initialise and queue the first user-space process.
///
/// Creates a [`Process`] with an empty address space, loads the embedded
/// ELF binary, creates a kernel-mode thread with an EL0-initialised context,
/// and queues it on the BSP core.
///
/// # Parameters
///
/// * `elf_data` — the embedded ELF binary (from `include_bytes!`).
/// * `elf_priority` — optional thread priority; defaults to mid-range.
///
/// # Panics
///
/// Panics on any error (the first process is mandatory).
pub(crate) fn init_first_process(
    elf_data: &[u8],
    elf_priority: Option<ThreadPriority>,
) -> Arc<Process> {
    // 1. Create Process with empty address space.  PID 1 = init process.
    let mut process = Process::try_new(1).expect("Failed to create Process");

    // 2. Load ELF into the process address space.
    let loaded = load_user_elf(
        elf_data,
        // SAFETY: we hold a unique `Arc<Process>` with refcount 1, so
        // `TinyArc::get_mut` succeeds and gives us exclusive access.
        &mut Arc::get_mut(&mut process)
            .expect("process must have unique ownership")
            .address_space,
    )
    .expect("Failed to load user ELF");

    // 3. Create a kernel-mode thread.
    //
    // We use a minimal kernel stack (Context + some margin) since the
    // thread will trap into EL0 immediately.  The stack only needs to
    // hold the saved context and the eret path.
    const MIN_KERNEL_STACK: usize = 2048;
    let kernel_stack = Stack::from_size(MIN_KERNEL_STACK)
        .expect("Failed to allocate kernel stack for user thread");
    let priority = elf_priority.unwrap_or(crate::config::MAX_THREAD_PRIORITY / 2);

    // Build a thread with an EL1 entry (empty wrapper), then patch the
    // Context on the kernel stack to target EL0.
    let thread = thread::Builder::new(Entry::C(enter_el0_helper))
        .set_priority(priority)
        .set_stack(kernel_stack)
        .build();

    // 4. Patch the saved Context for EL0 entry.
    //
    // Thread::init placed a Context on the kernel stack with SPSR = EL1h.
    // We overwrite it with EL0t settings.
    {
        let mut w = thread.lock();
        let saved_sp = w.saved_sp();
        // The Context is at saved_sp (aligned).
        let ctx = unsafe { &mut *(saved_sp as *mut Context) };
        ctx.init_el0(loaded.entry, loaded.stack_top);
        // Ensure the thread starts with IDLE state (Builder set it to READY).
        // SAFETY: we hold the lock, no concurrent access.
        unsafe { w.set_state(thread::IDLE) };
    }

    // 5. Attach thread to process.
    Process::attach_thread(&mut process, &thread);

    // 6. Queue the thread ready on the BSP core.
    scheduler::queue_ready_thread(thread::IDLE, thread.clone())
        .expect("Failed to queue first user thread");

    log::info!(
        "init_first_process: EL0 thread queued, entry={:#x} stack_top={:#x}",
        loaded.entry, loaded.stack_top
    );

    process
}

// ---------------------------------------------------------------------------
// EL0 entry trampoline
// ---------------------------------------------------------------------------

/// Minimal EL1 entry that does nothing — the real entry point is set directly
/// in the patched Context so the thread enters EL0 on first dispatch.
///
/// This function should never actually be called; it exists only because
/// `Thread::init` / `Builder` requires an `Entry`.  The saved Context is
/// overwritten with EL0 state before the thread is first scheduled.
extern "C" fn enter_el0_helper() {
    // Unreachable: the Context was patched to eret into EL0.
    // If reached, something went wrong with the context patching.
    unreachable!("enter_el0_helper called: EL0 context not patched correctly");
}