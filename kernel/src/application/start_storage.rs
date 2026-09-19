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

//! Pinned application start storage.
//!
//! [`ApplicationStartStorage`] owns every byte the `blueos_scrt1` entry needs
//! and keeps it stable after `launch` returns: the NUL-terminated argv/envp
//! strings, their C-style pointer arrays, the `execfn` path, the auxv table,
//! and the init/fini target arrays. It is held by the [`ThreadGroup`] for the
//! lifetime of the application — never on the launch closure's stack — so the
//! pointers inside [`BlueOsApplicationStartInfo`] stay valid until the last
//! thread exits.
//!
//! Every pointer inside the start-info block points into one of the owned heap
//! slices, whose contents never move, so the value can be copied around safely.
//! The block is built only after every allocation and pointer fix-up completed:
//! a failure at any step drops the partial storage and returns the error.

use alloc::{boxed::Box, vec::Vec};
use core::slice;

use blueos_header::application::{
    auxv, BlueOsApplicationStartInfo, BlueOsAuxvEntry, BlueOsFunctionPlan, BlueOsStringView,
    APPLICATION_START_INFO_ABI_VERSION, FUNCTION_PLAN_ABI_VERSION,
};
use blueos_loader::{LinkProduct, TargetAddress};

use crate::application::publication::KernelLinkReceipt;

/// Errors constructing [`ApplicationStartStorage`] without panicking.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StartStorageError {
    OutOfMemory,
}

/// Owned, pinned application start storage.
pub struct ApplicationStartStorage {
    _argv_bytes: Box<[u8]>,
    _envp_bytes: Box<[u8]>,
    _argv_ptrs: Box<[*const core::ffi::c_char]>,
    _envp_ptrs: Box<[*const core::ffi::c_char]>,
    _execfn_bytes: Box<[u8]>,
    _auxv: Box<[BlueOsAuxvEntry]>,
    _init_targets: Box<[usize]>,
    _fini_targets: Box<[usize]>,
    // Keep the start-info block in its own allocation. `ApplicationService`
    // takes its address before moving this storage into the thread group; an
    // inline field would move with `Self` and leave the new thread holding a
    // pointer into the launcher's dead stack frame.
    start_info: Box<[BlueOsApplicationStartInfo]>,
}

// SAFETY: every raw pointer in this struct (including the nested ones inside
// `start_info`) points into one of the `Box`-owned buffers above, which are
// exclusively owned, never moved after `build`, and only ever read through
// the pointers. Moving the struct to another thread therefore moves the
// backing allocations along with it; no pointer aliases thread-local state.
unsafe impl Send for ApplicationStartStorage {}

// SAFETY: the same argument as `Send` above, plus immutability. Every byte this
// struct owns is written only inside `build`; afterwards the only accessor that
// exposes a pointer is `start_info_ptr`, which takes `&self` and returns a
// `*const`, and there is no `&mut self` method at all. Sharing
// `&ApplicationStartStorage` between threads can therefore only ever produce
// reads of buffers that outlive the borrow.
//
// This is needed because the kernel's `sync::SpinLock<T>` is `Sync` only when
// `T: Sync`, so a `ThreadGroup` (which holds one of these) has to be `Sync` to
// sit behind it. The vendored `spin::Mutex<T>` is `Sync` for `T: Send`, which
// is why the group could hold this before the lock was made interrupt-saving.
unsafe impl Sync for ApplicationStartStorage {}

impl ApplicationStartStorage {
    /// Build the start storage from an owned launch request's content plus the
    /// committed link result.
    ///
    /// `argv`/`envp` are the bounded string views already validated by the
    /// launch syscall copy-in; `path` is the application path (for `AT_EXECFN`).
    /// `page_granule` is the memory backend's protection granule (for
    /// `AT_PAGESZ`), derived from `ImageProtectionMemory::protection_capabilities`.
    pub fn build(
        path: &[u8],
        argv: &[BlueOsStringView],
        envp: &[BlueOsStringView],
        product: &LinkProduct<KernelLinkReceipt>,
        page_granule: u64,
    ) -> Result<Self, StartStorageError> {
        let (argv_bytes, argv_ptrs) = build_strings(argv)?;
        let (envp_bytes, envp_ptrs) = build_strings(envp)?;

        let execfn_bytes = nul_terminated(path)?;
        let execfn_ptr = execfn_bytes.as_ptr();
        let entry = product.entry();
        let program_headers = root_program_headers(product);
        // The application runs the startup plan and, at exit,
        // only the root/private fini — a system DSO's destructors belong to
        // the registry's instance reap, never to an application exit.
        let init_targets = build_plan_targets(product.lifecycle_plans().startup().iter())?;
        let fini_targets = build_plan_targets(product.lifecycle_plans().group_fini().iter())?;

        let (auxv, auxv_count) = build_auxv(entry, program_headers, execfn_ptr, page_granule)?;

        let init_plan = BlueOsFunctionPlan {
            abi_version: FUNCTION_PLAN_ABI_VERSION,
            struct_size: core::mem::size_of::<BlueOsFunctionPlan>() as u32,
            entries: init_targets.as_ptr(),
            count: init_targets.len(),
        };
        let fini_plan = BlueOsFunctionPlan {
            abi_version: FUNCTION_PLAN_ABI_VERSION,
            struct_size: core::mem::size_of::<BlueOsFunctionPlan>() as u32,
            entries: fini_targets.as_ptr(),
            count: fini_targets.len(),
        };

        let start_info = BlueOsApplicationStartInfo {
            abi_version: APPLICATION_START_INFO_ABI_VERSION,
            struct_size: core::mem::size_of::<BlueOsApplicationStartInfo>() as u32,
            argc: argv.len(),
            argv: argv_ptrs.as_ptr(),
            envc: envp.len(),
            envp: envp_ptrs.as_ptr(),
            auxv: auxv.as_ptr(),
            auxv_count,
            init_plan,
            fini_plan,
        };
        let mut pinned_start_info = Vec::new();
        pinned_start_info
            .try_reserve_exact(1)
            .map_err(|_| StartStorageError::OutOfMemory)?;
        pinned_start_info.push(start_info);

        Ok(Self {
            _argv_bytes: argv_bytes,
            _envp_bytes: envp_bytes,
            _argv_ptrs: argv_ptrs,
            _envp_ptrs: envp_ptrs,
            _execfn_bytes: execfn_bytes,
            _auxv: auxv,
            _init_targets: init_targets,
            _fini_targets: fini_targets,
            start_info: pinned_start_info.into_boxed_slice(),
        })
    }

    /// A stable raw pointer to the block, for the thread entry argument.
    #[inline]
    pub fn start_info_ptr(&self) -> *const BlueOsApplicationStartInfo {
        self.start_info.as_ptr()
    }
}

type OwnedStrings = (Box<[u8]>, Box<[*const core::ffi::c_char]>);

/// Build the NUL-terminated string pool and C-style pointer array for a set of
/// bounded string views. The returned pointer array is `len + 1` slots with a
/// null terminator, matching the POSIX `main(argc, argv)` shape.
fn build_strings(views: &[BlueOsStringView]) -> Result<OwnedStrings, StartStorageError> {
    let mut total = 0usize;
    for view in views {
        total = total
            .checked_add(view.len)
            .and_then(|v| v.checked_add(1))
            .ok_or(StartStorageError::OutOfMemory)?;
    }

    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(total)
        .map_err(|_| StartStorageError::OutOfMemory)?;
    let mut offsets = Vec::new();
    offsets
        .try_reserve_exact(views.len())
        .map_err(|_| StartStorageError::OutOfMemory)?;
    for view in views {
        offsets.push(bytes.len());
        // SAFETY: `view` is a validated view whose `data`/`len` the launch
        // copy-in already proved to reference a readable, counted range in the
        // caller's registered image/stack/heap.
        let src = unsafe { slice::from_raw_parts(view.data, view.len) };
        bytes.extend_from_slice(src);
        bytes.push(0);
    }

    let bytes: Box<[u8]> = bytes.into_boxed_slice();
    let base = bytes.as_ptr();
    let mut ptrs = Vec::new();
    ptrs.try_reserve_exact(views.len() + 1)
        .map_err(|_| StartStorageError::OutOfMemory)?;
    for offset in offsets {
        // SAFETY: `base` points into the owned `bytes` heap slice, whose
        // contents are immutable from here on; `offset` is a recorded index
        // into it.
        ptrs.push(unsafe { base.add(offset) } as *const core::ffi::c_char);
    }
    ptrs.push(core::ptr::null());
    Ok((bytes, ptrs.into_boxed_slice()))
}

/// Copy a byte slice into a fresh NUL-terminated buffer.
fn nul_terminated(bytes: &[u8]) -> Result<Box<[u8]>, StartStorageError> {
    let mut buffer = Vec::new();
    buffer
        .try_reserve_exact(bytes.len() + 1)
        .map_err(|_| StartStorageError::OutOfMemory)?;
    buffer.extend_from_slice(bytes);
    buffer.push(0);
    Ok(buffer.into_boxed_slice())
}

/// Flatten an init/fini plan into a boxed array of runtime function addresses
/// (Thumb bit preserved on ARM).
fn build_plan_targets<'a, I>(plan: I) -> Result<Box<[usize]>, StartStorageError>
where
    I: IntoIterator<Item = &'a blueos_loader::LifecycleEntry>,
{
    let mut targets = Vec::new();
    for entry in plan {
        targets
            .try_reserve(1)
            .map_err(|_| StartStorageError::OutOfMemory)?;
        targets.push(entry.function().get() as usize);
    }
    Ok(targets.into_boxed_slice())
}

/// The root image's program-header summary, for `AT_PHDR/AT_PHENT/AT_PHNUM`.
///
/// The root is the committed image with `owner == 0`; a link result
/// always has exactly one.
fn root_program_headers(
    product: &LinkProduct<KernelLinkReceipt>,
) -> blueos_loader::ProgramHeaderRuntimeInfo {
    product
        .context()
        .images()
        .iter()
        .find(|image| image.owner().get() == 0)
        .map(|image| *image.descriptor().program_headers())
        .unwrap_or_else(blueos_loader::ProgramHeaderRuntimeInfo::empty)
}

/// Build the auxv table (plus a `AT_NULL` terminator) and return it with its
/// length.
fn build_auxv(
    entry: TargetAddress,
    program_headers: blueos_loader::ProgramHeaderRuntimeInfo,
    execfn_ptr: *const u8,
    page_granule: u64,
) -> Result<(Box<[BlueOsAuxvEntry]>, usize), StartStorageError> {
    let mut auxv = Vec::new();
    auxv.try_reserve_exact(8)
        .map_err(|_| StartStorageError::OutOfMemory)?;

    // Thumbv7 uses ELF32, so every validated target address must fit `usize`.
    // `usize` after the canonical range check.
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_ENTRY,
        value: entry.get() as usize,
    });
    if let Some(phdr) = program_headers.runtime_vaddr() {
        auxv.push(BlueOsAuxvEntry {
            key: auxv::AT_PHDR,
            value: phdr.get() as usize,
        });
    }
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_PHENT,
        value: program_headers.entry_size() as usize,
    });
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_PHNUM,
        value: program_headers.count() as usize,
    });
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_PAGESZ,
        value: page_granule as usize,
    });
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_EXECFN,
        value: execfn_ptr as usize,
    });
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_BLUEOS_ABI_VERSION,
        value: APPLICATION_START_INFO_ABI_VERSION as usize,
    });
    auxv.push(BlueOsAuxvEntry {
        key: auxv::AT_NULL,
        value: 0,
    });

    let count = auxv.len();
    Ok((auxv.into_boxed_slice(), count))
}
