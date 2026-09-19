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

//! Versioned application start/exit wire ABI.
//!
//! These are the `#[repr(C)]` structs passed across the SWI boundary between a
//! dynamic application (running `blueos_scrt1`/`librs`) and the kernel's
//! [`ApplicationManager`]. Every multi-word request and response begins with a
//! `abi_version`/`struct_size` prefix so a v1 consumer can accept a larger
//! future `struct_size` (appended, read-only fields) and reject a smaller one
//! that lacks the required prefix — new fields may only be appended, never
//! inserted or reordered.
//!
//! Start information is *not* a Linux initial stack: `argc` is not assumed to
//! sit on top of `sp`; the kernel pins every
//! nested pointer in [`BlueOsApplicationStartInfo`] in `ApplicationStartStorage`
//! before the main thread is scheduled.

use core::ffi::c_char;

/// v1 of the application start-information block.
pub const APPLICATION_START_INFO_ABI_VERSION: u32 = 1;

/// v1 of the application launch request.
pub const APPLICATION_LAUNCH_REQUEST_ABI_VERSION: u32 = 1;

/// v1 of a [`BlueOsFunctionPlan`] constructor/destructor block.
pub const FUNCTION_PLAN_ABI_VERSION: u32 = 1;

/// A counted byte range passed across the SWI boundary without a NUL-termination
/// requirement. `len` is the byte length; `data` may not be null when `len` is
/// non-zero.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BlueOsStringView {
    pub data: *const u8,
    pub len: usize,
}

/// One `auxv` entry. The kernel fills the array in `ApplicationStartStorage`;
/// `librs::getauxval` searches it per application, never through a process-global
/// pointer that two applications could overwrite.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BlueOsAuxvEntry {
    pub key: usize,
    pub value: usize,
}

/// A constructor/destructor plan: an array of target entry addresses (Thumb bit
/// preserved on ARM) plus its own version/size prefix. The array is pinned for
/// the lifetime of the application; librs walks it outside every loader lock
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BlueOsFunctionPlan {
    pub abi_version: u32,
    pub struct_size: u32,
    pub entries: *const usize,
    pub count: usize,
}

/// The pinned start-information block handed to `blueos_scrt1::_start`
///
/// `argv`/`envp` are C-style `char **`-equivalent pointer arrays (the shape
/// POSIX `main(argc, argv, envp)` expects); `argc`/`envc` are their exact
/// lengths. `auxv`/`init_plan`/`fini_plan` are pinned in the kernel's start
/// storage before the main thread runs, so every nested pointer stays stable
/// after `launch` returns. The application path is exposed through
/// `AT_EXECFN`. Any future field must be appended and gated by `struct_size`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BlueOsApplicationStartInfo {
    pub abi_version: u32,
    pub struct_size: u32,
    pub argc: usize,
    pub argv: *const *const c_char,
    pub envc: usize,
    pub envp: *const *const c_char,
    pub auxv: *const BlueOsAuxvEntry,
    pub auxv_count: usize,
    pub init_plan: BlueOsFunctionPlan,
    pub fini_plan: BlueOsFunctionPlan,
}

/// The bounded launch request a dynamic application sends to start another
/// application. `librs::spawn` converts POSIX inputs into this shape;
/// the kernel copies a fixed-size header, validates counts/byte totals/string
/// limits, then copies the content into an owned request. It never scans
/// an unbounded C pointer array from the handler itself.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BlueOsApplicationLaunchRequest {
    pub abi_version: u32,
    pub struct_size: u32,
    pub path: BlueOsStringView,
    pub argv: *const BlueOsStringView,
    pub argc: usize,
    pub envp: *const BlueOsStringView,
    pub envc: usize,
}

/// Auxiliary-vector keys shared by the kernel and `librs`.
///
/// The first block reuses the platform ELF auxiliary conventions so
/// `getauxval` behaves as a dynamic application expects; the `AT_BLUEOS_*`
/// key is BlueOS-specific and sits far above the standard range to avoid a
/// collision as the standard table grows.
pub mod auxv {
    pub const AT_NULL: usize = 0;
    pub const AT_PHDR: usize = 3;
    pub const AT_PHENT: usize = 4;
    pub const AT_PHNUM: usize = 5;
    pub const AT_PAGESZ: usize = 6;
    pub const AT_ENTRY: usize = 9;
    pub const AT_EXECFN: usize = 31;

    /// The `abi_version` of the start-information block this app received.
    pub const AT_BLUEOS_ABI_VERSION: usize = 0x1001;
}
