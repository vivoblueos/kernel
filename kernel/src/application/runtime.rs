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

//! Boot-time dynamic application runtime assembly.
//!
//! [`super::seed`] installs the system image into the VFS. This
//! module independently assembles the loader, registry, manager and reaper
//! over the fixed system-library catalog, and later launches the bootstrap
//! shell from the dedicated kernel image.

use alloc::vec::Vec;

use crate::application::{
    adapters::system_paths::{SystemLibraryEntry, SystemLibraryPaths},
    service::ApplicationService,
};

/// The fixed system library catalog used after private-library lookup. The
/// scope test DSO is unloadable; libc remains cached for the system lifetime.
static SYSTEM_LIBRARIES: &[SystemLibraryEntry] = &[
    SystemLibraryEntry {
        lookup_name: b"libc.so.1",
        path: "/system/lib/libc.so.1",
        // Keep the process runtime DSO resident. Its global state and possible
        // address escapes are not modeled well enough to prove unloading safe.
        keep_cached: true,
    },
    SystemLibraryEntry {
        // This fixture deliberately has no DT_SONAME. Linking records its
        // build filename while the catalog path remains the stable registry
        // key, proving that lookup metadata and ELF metadata are independent.
        lookup_name: b"libscope_sys.so",
        path: "/system/lib/libscope_sys.so.1",
        // The scope corpus's test system DSO has no escapes: the
        // reaper runs its fini and unloads it on quiescence, and the next
        // launch reloads generation+1.
        keep_cached: false,
    },
];
static CATALOG: SystemLibraryPaths = SystemLibraryPaths::new(SYSTEM_LIBRARIES);

/// Initialize the dynamic application runtime over the installed system image.
///
/// This does not write or replace any VFS file. The underlying service is a
/// `Once` singleton, so later calls return the already assembled runtime.
pub fn init() -> &'static ApplicationService {
    ApplicationService::init(&CATALOG)
}

/// Launch the dynamic bootstrap shell from the dedicated boot image.
///
/// Boot must have called [`init`] first. A launch failure is logged but is not
/// fatal: the runtime stays available for diagnostics or a later explicit
/// spawn.
pub fn launch_bootstrap_shell() {
    let service = ApplicationService::get()
        .expect("dynamic application runtime must be initialized before launching the shell");
    let argv = alloc::vec![b"/apps/shell/app.elf".to_vec()];
    if let Err(error) = service.spawn("/apps/shell/app.elf", argv, Vec::new()) {
        log::error!("boot: bootstrap shell launch failed: {:?}", error);
    }
}

/// The system catalog used by the boot-time dynamic application runtime.
pub fn catalog() -> &'static SystemLibraryPaths {
    &CATALOG
}
