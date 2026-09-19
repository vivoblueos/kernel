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

//! Boot-time system image seeding.
//!
//! The system image (`/system/lib/libc.so.1` and the application bundles) is
//! read from the build's output directory over semihosting and copied into the
//! root tmpfs here. Nothing is embedded in the kernel image: the artifacts stay
//! ordinary files on the host, and the loader later opens their tmpfs copies
//! through the normal VFS path.
//!
//! Semihosting is a debug channel, so this is the development/QEMU delivery
//! route. A board with real block storage should install the image from there
//! instead and leave `boot_dynamic_seed` off — the loader backend does not
//! depend on this module.
//!
//! Only images whose runner enables semihosting may call [`install`]; an
//! unhandled semihosting trap faults the CPU.
//!
//! [`super::runtime`] separately assembles the loader-facing application
//! service over the seeded paths.

use core::ffi::{c_char, CStr};

/// Longest VFS path this module can install, including the NUL terminator.
const MAX_PATH_BYTES: usize = 64;

/// Streaming chunk size for the host-to-tmpfs copy. The copy is chunked so a
/// multi-megabyte debug build of `libc.so.1` never has to be resident twice.
const SEED_CHUNK: usize = 4096;

/// Copy `path` into a NUL-terminated buffer, or report that it does not fit.
fn c_path(path: &str, buf: &mut [u8; MAX_PATH_BYTES]) -> Option<*const c_char> {
    if path.len() >= buf.len() {
        log::error!(
            "boot seed: VFS path of {} bytes exceeds the {}-byte limit: {}",
            path.len(),
            buf.len() - 1,
            path
        );
        return None;
    }
    buf[..path.len()].copy_from_slice(path.as_bytes());
    buf[path.len()] = 0;
    Some(buf.as_ptr() as *const c_char)
}

/// Create the parent directories of `path` inside the root tmpfs, best effort
/// (already-exists errors are fine). Only *parents* are created: the last
/// component is the file itself.
fn mkdirs(path: &str) {
    let mut buf = [0u8; MAX_PATH_BYTES];
    let mut prefix_end = 1; // skip the leading '/'
    while prefix_end < path.len() {
        let slash = match path[prefix_end..].find('/') {
            Some(at) => prefix_end + at,
            // The last component is the seeded file, not a directory.
            None => break,
        };
        let Some(dir) = c_path(&path[..slash], &mut buf) else {
            return;
        };
        // SAFETY: `dir` points into `buf`, which holds a NUL-terminated copy of
        // the directory prefix for the duration of the call.
        let _ = unsafe { crate::vfs::syscalls::mkdir(dir, 0o755) };
        prefix_end = slash + 1;
    }
}

/// Stream `host_path` into a fresh VFS file at `vfs_path`, replacing any
/// previous content. Returns the number of bytes installed.
fn seed_host_file(vfs_path: &str, host_path: &CStr) -> usize {
    let Ok(mut source) = semihosting::fs::File::open(host_path) else {
        log::warn!("boot seed: cannot open host file {:?}", host_path);
        return 0;
    };

    mkdirs(vfs_path);
    let mut path_buf = [0u8; MAX_PATH_BYTES];
    let Some(c_path) = c_path(vfs_path, &mut path_buf) else {
        return 0;
    };

    // SAFETY: `c_path` points into `path_buf`, which holds a NUL-terminated
    // copy of `vfs_path` for the duration of the calls below.
    unsafe {
        let fd = crate::vfs::syscalls::open(
            c_path,
            libc::O_CREAT | libc::O_WRONLY | libc::O_TRUNC,
            0o644,
        );
        if fd < 0 {
            log::warn!("boot seed: open {} failed ({})", vfs_path, fd);
            return 0;
        }

        let mut installed = 0usize;
        let mut chunk = [0u8; SEED_CHUNK];
        loop {
            let read = match semihosting::io::Read::read(&mut source, &mut chunk) {
                Ok(0) => break,
                Ok(read) => read,
                Err(_) => {
                    log::error!(
                        "boot seed: reading {:?} failed after {} bytes",
                        host_path,
                        installed
                    );
                    installed = 0;
                    break;
                }
            };
            let written = crate::vfs::syscalls::write(fd, chunk.as_ptr(), read);
            if written != read as isize {
                log::error!(
                    "boot seed: writing {} truncated at {} bytes ({} of {})",
                    vfs_path,
                    installed,
                    written,
                    read
                );
                installed = 0;
                break;
            }
            installed += read;
        }
        crate::vfs::syscalls::close(fd);
        installed
    }
}

/// Install the system image into the root tmpfs.
///
/// Called by the images that need it — the dedicated boot image and the
/// dynamic-application tests — after the VFS is initialized and before the
/// loader is asked to launch anything. Reinstalling replaces the files at the
/// same paths.
///
/// A file that cannot be installed is logged and skipped rather than treated as
/// fatal, so a partially seeded root still boots far enough to report why. The
/// subsequent launch of a missing application then fails with its own error.
pub fn install() {
    for entry in boot_seed_catalog::FILES {
        let installed = seed_host_file(entry.path, entry.host_path);
        if installed > 0 {
            log::debug!("boot seed: {} <- {} bytes", entry.path, installed);
        }
    }
}
