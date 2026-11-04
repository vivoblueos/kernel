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

use crate::{
    error::Error,
    vfs::{
        dcache::Dcache,
        fs::FileSystem,
        inode_mode::{InodeFileType, InodeMode},
        mount::get_mount_manager,
        tmpfs::TmpFileSystem,
    },
};
use log::debug;

mod dcache;
mod devfs;
pub mod dirent;
#[cfg(fatfs)]
mod fatfs;
pub mod fd_manager;
mod file;
mod fs;
mod inode;
mod inode_mode;
mod mount;
mod path;
pub mod pipe;
pub mod poll;
#[cfg(procfs)]
mod procfs;
#[cfg(procfs)]
pub use procfs::{trace_thread_close, trace_thread_create};
mod root;
#[cfg(enable_net)]
mod sockfs;
pub mod syscalls;
/// Translation of pointers the caller passed in a syscall. See the module docs
/// for why a bare dereference is not an option once U-mode exists.
pub mod uptr;
mod tmpfs;
mod utils;
use alloc::string::String;
pub use file::AccessMode;
#[cfg(enable_net)]
pub use sockfs::{alloc_sock_fd, free_sock_fd, get_sock_by_fd, sock_attach_to_fd};

#[cfg(fatfs)]
fn should_skip_fatfs_mount(policy: crate::boards::BlockStoragePolicy, error: Error) -> bool {
    policy.allows_missing() && error == crate::error::code::ENODEV
}

/// Read an entire file into memory, refusing anything larger than `max`.
///
/// Used by `execve` and by the kernel-side spawn path: both need the whole
/// image before they can parse it, and both must bound the read so a bogus
/// size field cannot exhaust the heap in one allocation.
///
/// The cap is enforced *while* reading rather than from `stat`, because a file
/// can grow between the two calls and the reader would then get less than it
/// promised itself.
pub fn read_whole_file(path: &str, max: usize) -> Result<alloc::vec::Vec<u8>, Error> {
    use crate::vfs::file::FileOps;
    // Fully qualified: the parameter is also named `path`, and a bare `path::`
    // would resolve to the argument, not the module.
    let file = crate::vfs::path::open_path(path, libc::O_RDONLY, 0)?;
    let mut out = alloc::vec::Vec::new();
    let mut buf = [0u8; 4096];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        if out.len() + n > max {
            return Err(crate::error::code::EINVAL);
        }
        out.extend_from_slice(&buf[..n]);
    }
    Ok(out)
}

/// Create a directory, treating "already there" as success.
///
/// The boot path that installs the user images runs once, but it runs on every
/// reset of a machine whose filesystem may survive the reset; an `EEXIST` here
/// is the normal case, not an error.
pub fn ensure_dir(path: &str) -> Result<(), Error> {
    let Some((dir, name)) = crate::vfs::path::find_parent_and_name(path) else {
        return Err(crate::error::code::EINVAL);
    };
    match dir.new_child(
        name,
        InodeFileType::Directory,
        InodeMode::from(0o755u32),
        || None,
    ) {
        Ok(_) => Ok(()),
        Err(e) if e == crate::error::code::EEXIST => Ok(()),
        Err(e) => Err(e),
    }
}

/// Write `bytes` to `path`, creating or truncating it.
///
/// One `write` is not guaranteed to consume the whole buffer — a pipe, a
/// socket and a nearly full filesystem all return short counts — so the loop
/// is the contract, not defensive coding.
pub fn install_file(path: &str, bytes: &[u8]) -> Result<(), Error> {
    use crate::vfs::file::FileOps;
    let file = crate::vfs::path::open_path(
        path,
        libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
        0o755,
    )?;
    let mut written = 0;
    while written < bytes.len() {
        let n = file.write(&bytes[written..])?;
        if n == 0 {
            return Err(crate::error::code::EIO);
        }
        written += n;
    }
    Ok(())
}

/// Initialize the virtual file system
pub fn vfs_init() -> Result<(), Error> {    debug!("Initializing VFS...");
    root::init();
    let cwd = path::get_working_dir();

    // /dev is a temporary filesystem
    let dev_name = String::from("dev");
    let devfs = TmpFileSystem::new();
    // create the directory /dev
    let dev_dir = cwd.new_child(
        dev_name.as_str(),
        InodeFileType::Directory,
        InodeMode::from(0o555),
        || None,
    )?;
    let devfs_mount_point = Dcache::new(devfs.root_inode(), dev_name, cwd.get_weak_ref());
    devfs_mount_point.mount(devfs)?;
    debug!("Mounted devfs at '/dev'");
    devfs::init()?;

    // Stdio (fds 0/1/2 on the root process's fd table) is now initialized in
    // the boot path after the root process is created, since it requires the
    // per-process `Process::fd_manager` rather than a global singleton.

    #[cfg(fatfs)]
    {
        use crate::{
            boards::{BLOCK_STORAGE_DEVICE_NAME, BLOCK_STORAGE_MOUNT_POINT, BLOCK_STORAGE_POLICY},
            vfs::{fatfs::FatFileSystem, fs::FileSystem},
        };
        use alloc::string::String;

        debug!("init fatfs");
        match FatFileSystem::new(BLOCK_STORAGE_DEVICE_NAME) {
            Ok(fatfs) => {
                let fat_name = String::from(BLOCK_STORAGE_MOUNT_POINT);
                let dev_dir = cwd.new_child(
                    fat_name.as_str(),
                    InodeFileType::Directory,
                    InodeMode::from(0o555),
                    || None,
                )?;
                let fatfs_mount_point =
                    Dcache::new(fatfs.root_inode(), fat_name, cwd.get_weak_ref());
                fatfs_mount_point.mount(fatfs)?;
                debug!("Mounted fatfs at '/{}'", BLOCK_STORAGE_MOUNT_POINT);
            }
            Err(error) if should_skip_fatfs_mount(BLOCK_STORAGE_POLICY, error) => {}
            Err(error) => return Err(error),
        }
    }

    #[cfg(procfs)]
    {
        let proc_name = String::from("proc");
        let procfs = procfs::get_procfs();
        let proc_dir = cwd.new_child(
            proc_name.as_str(),
            InodeFileType::Directory,
            InodeMode::from(0o555),
            || None,
        )?;
        let procfs_mount_point = Dcache::new(procfs.root_inode(), proc_name, cwd.get_weak_ref());
        procfs_mount_point.mount(procfs.clone())?;
        debug!("Mounted procfs at '/proc'");
    }

    debug!("VFS initialized successfully");
    Ok(())
}
