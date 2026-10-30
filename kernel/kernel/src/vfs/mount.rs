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

#[cfg(fatfs)]
use crate::vfs::fatfs::FatFileSystem;
#[cfg(procfs)]
use crate::vfs::procfs::ProcFileSystem;
use crate::{
    error::{code, Error},
    vfs::{dcache::Dcache, fs::FileSystem, tmpfs::TmpFileSystem},
};

use alloc::{collections::BTreeMap, string::String, sync::Arc, vec::Vec};
use log::{debug, error, warn};
use spin::{Once, RwLock as SpinRwLock};

/// Mount point information
#[derive(Clone)]
pub struct MountPoint {
    /// Root directory entry
    pub root: Arc<Dcache>,
    /// Filesystem instance
    pub fs: Arc<dyn FileSystem>,
}

/// Mount point manager
#[cfg_attr(feature = "cbindgen", no_mangle)]
pub struct MountManager {
    /// List of mount points, sorted by path length in descending order to ensure longest match priority
    mount_points: SpinRwLock<BTreeMap<String, Arc<MountPoint>>>,
}

impl MountManager {
    pub fn new() -> Self {
        Self {
            mount_points: SpinRwLock::new(BTreeMap::new()),
        }
    }

    /// Add a mount point
    pub fn add_mount(
        &self,
        path: &String,
        root: Arc<Dcache>,
        fs: Arc<dyn FileSystem>,
    ) -> Result<(), Error> {
        let mut mounts = self.mount_points.write();
        if mounts.contains_key(path) {
            warn!("[mount_manager] Mount point already exists: {}", path);
            return Err(code::EEXIST);
        }

        mounts.insert(path.clone(), Arc::new(MountPoint { root, fs }));

        debug!("[mount_manager] Added mount point: {}", path);
        Ok(())
    }

    pub fn remove_mount(&self, path: &String) -> Result<(), Error> {
        let mut mounts = self.mount_points.write();
        mounts.remove(path);
        Ok(())
    }

    pub fn find_mount(&self, path: &String) -> Option<Arc<MountPoint>> {
        self.mount_points.read().get(path).cloned()
    }

    /// Get all mount points
    pub fn list_mounts(&self) -> Vec<Arc<MountPoint>> {
        self.mount_points.read().values().cloned().collect()
    }
}

/// Global mount manager instance
static MOUNT_MANAGER: Once<MountManager> = Once::new();
/// Get mount manager instance
#[inline(always)]
pub fn get_mount_manager() -> &'static MountManager {
    MOUNT_MANAGER.call_once(MountManager::new)
}

pub fn get_fs(fs_type: &str, device: &str) -> Option<Arc<dyn FileSystem>> {
    match fs_type {
        "tmpfs" => Some(TmpFileSystem::new()),
        #[cfg(fatfs)]
        "fatfs" => match FatFileSystem::new(device) {
            Ok(fs) => Some(fs),
            Err(error) => {
                error!(
                    "Fail to init fat file system with device {}, {}",
                    device, error
                );
                None
            }
        },
        _ => None,
    }
}
