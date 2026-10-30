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
    vfs::{dcache::Dcache, inode::InodeOps},
};
use alloc::sync::Arc;
use core::{any::Any, fmt::Debug};

/// File system information, used for statfs
#[derive(Debug, Clone, Default)]
pub struct FileSystemInfo {
    pub magic: usize,
    pub dev: usize,
    pub namelen: usize,
    pub bsize: usize,
    pub frsize: usize,
    pub blocks: usize,
    pub bfree: usize,
    pub bavail: usize,
    pub files: usize,
    pub ffree: usize,
    pub favail: usize,
    pub fsid: u64,
    pub flags: usize,
}

impl FileSystemInfo {
    pub fn new(
        magic: usize,
        dev: usize,
        name_max_len: usize,
        block_size: usize,
        block_num: usize,
    ) -> Self {
        Self {
            dev,
            magic,
            namelen: name_max_len,
            bsize: block_size,
            frsize: block_size,
            blocks: block_num,
            ..Default::default()
        }
    }
}

/// File system trait
pub trait FileSystem: Any + Send + Sync {
    fn mount(&self, mount_point: Arc<Dcache>) -> Result<(), Error>;

    fn unmount(&self) -> Result<(), Error>;

    fn sync(&self) -> Result<(), Error>;

    fn root_inode(&self) -> Arc<dyn InodeOps>;

    fn fs_info(&self) -> FileSystemInfo;

    fn fs_type(&self) -> &str;
}

impl dyn FileSystem {
    pub fn downcast_ref<T: FileSystem>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref::<T>()
    }
}

impl Debug for dyn FileSystem {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FileSystem")
            .field("fs_info", &self.fs_info())
            .field("fs_type", &self.fs_type())
            .finish()
    }
}
