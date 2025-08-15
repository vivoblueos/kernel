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
        fd_manager::get_fd_manager,
        fs::FileSystem,
        inode_mode::{InodeFileType, InodeMode},
        mount::get_mount_manager,
        tmpfs::TmpFileSystem,
    },
};
use log::{debug, error, warn};

mod dcache;
mod devfs;
pub mod dirent;
#[cfg(virtio)]
mod fatfs;
mod fd_manager;
mod file;
mod fs;
mod inode;
mod inode_mode;
mod mount;
mod path;
#[cfg(procfs)]
mod procfs;
#[cfg(procfs)]
pub use procfs::{trace_thread_close, trace_thread_create};
mod root;
mod sockfs;
pub mod syscalls;
mod tmpfs;
mod utils;
use alloc::string::String;
pub use file::AccessMode;
pub use sockfs::{alloc_sock_fd, free_sock_fd, get_sock_by_fd, sock_attach_to_fd};

/// Initialize the virtual file system
pub fn vfs_init() -> Result<(), Error> {
    debug!("Initializing VFS...");
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

    debug!("init stdio");
    let mut fd_manager = get_fd_manager().lock();
    fd_manager.init_stdio()?;

    #[cfg(virtio)]
    {
        use crate::{
            devices::block::VIRTUAL_STORAGE_NAME,
            vfs::{fatfs::FatFileSystem, fs::FileSystem},
        };
        use alloc::string::String;

        debug!("init fatfs");
        match FatFileSystem::new(VIRTUAL_STORAGE_NAME) {
            Ok(fatfs) => {
                let fat_name = String::from("fat");
                // create the directory /fat
                let dev_dir = cwd.new_child(
                    fat_name.as_str(),
                    InodeFileType::Directory,
                    InodeMode::from(0o555),
                    || None,
                )?;
                let fatfs_mount_point =
                    Dcache::new(fatfs.root_inode(), fat_name, cwd.get_weak_ref());
                fatfs_mount_point.mount(fatfs)?;
                debug!("Mounted fatfs at '/fat'");
            }
            Err(error) => {
                error!("Fail to init fat file system, {}", error);
                return Err(error);
            }
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
