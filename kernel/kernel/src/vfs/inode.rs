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
    devices::Device,
    error::{code, Error},
    vfs::{
        dirent::DirBufferReader,
        file::FileAttr,
        fs::FileSystem,
        inode_mode::{mode_t, InodeFileType, InodeMode},
    },
};
use alloc::{string::String, sync::Arc};
use core::{any::Any, fmt, time::Duration};
use log::warn;

/// Filesystem inode number
pub type InodeNo = usize;

/// Inode attributes
#[derive(Clone)]
pub struct InodeAttr {
    pub inode_no: InodeNo, // Index Node number
    pub size: usize,       // File size
    pub blk_size: usize,   // Block size
    pub blocks: usize,     // Number of blocks
    pub atime: Duration,   // Access time
    pub mtime: Duration,   // Modification time
    pub ctime: Duration,   // Creation time
    pub mode: mode_t,      // File type and access permissions
    pub nlinks: u32,       // Number of hard links
    pub uid: u32,          // User ID
    pub gid: u32,          // Group ID
}

impl InodeAttr {
    /// Create new inode attributes
    pub fn new(
        inode_no: InodeNo,
        file_type: InodeFileType,
        mode: InodeMode,
        uid: u32,
        gid: u32,
        blk_size: usize,
    ) -> Self {
        Self {
            inode_no,
            size: 0,
            blk_size,
            blocks: 0,
            atime: Default::default(),
            mtime: Default::default(),
            ctime: Default::default(),
            mode: file_type as u32 | mode.bits(),
            nlinks: if file_type == InodeFileType::Directory {
                2
            } else {
                1
            },
            uid,
            gid,
        }
    }

    pub fn ino(&self) -> InodeNo {
        self.inode_no
    }
    pub fn type_(&self) -> InodeFileType {
        InodeFileType::from(self.mode)
    }
    pub fn mode(&self) -> InodeMode {
        InodeMode::from(self.mode)
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn atime(&self) -> Duration {
        self.atime
    }
    pub fn set_atime(&mut self, time: Duration) {
        self.atime = time;
    }
    pub fn mtime(&self) -> Duration {
        self.mtime
    }
    pub fn set_mtime(&mut self, time: Duration) {
        self.mtime = time;
    }
    pub fn set_size(&mut self, size: usize) {
        self.size = size;
    }
}

impl fmt::Debug for InodeAttr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("InodeAttr")
            .field("inode_no", &self.inode_no)
            .field("size", &self.size)
            .field("blk_size", &self.blk_size)
            .field("blocks", &self.blocks)
            .field(
                "atime",
                &format_args!(
                    "{}.{:03}s",
                    self.atime.as_secs(),
                    self.atime.subsec_millis()
                ),
            )
            .field(
                "mtime",
                &format_args!(
                    "{}.{:03}s",
                    self.mtime.as_secs(),
                    self.mtime.subsec_millis()
                ),
            )
            .field(
                "ctime",
                &format_args!(
                    "{}.{:03}s",
                    self.ctime.as_secs(),
                    self.ctime.subsec_millis()
                ),
            )
            .field("mode", &self.mode)
            .field("nlinks", &self.nlinks)
            .field("uid", &self.uid)
            .field("gid", &self.gid)
            .finish()
    }
}

pub trait InodeOps: Any + Sync + Send {
    fn read_at(&self, offset: usize, buf: &mut [u8], nonblock: bool) -> Result<usize, Error> {
        warn!("read_at is not implemented");
        Err(code::EINVAL)
    }
    fn write_at(&self, offset: usize, buf: &[u8], nonblock: bool) -> Result<usize, Error> {
        warn!("write_at is not implemented");
        Err(code::EINVAL)
    }
    fn link(&self, old: &Arc<dyn InodeOps>, name: &str) -> Result<(), Error> {
        warn!("link is not implemented");
        Err(code::ENOTDIR)
    }
    fn unlink(&self, name: &str) -> Result<(), Error> {
        warn!("unlink is not implemented");
        Err(code::ENOTDIR)
    }
    fn rmdir(&self, name: &str) -> Result<(), Error> {
        warn!("rmdir is not implemented");
        Err(code::ENOTDIR)
    }
    fn rename(
        &self,
        old_name: &str,
        target: &Arc<dyn InodeOps>,
        new_name: &str,
    ) -> Result<(), Error> {
        warn!("rename is not implemented");
        Err(code::ENOTDIR)
    }
    fn getdents_at(&self, offset: usize, reader: &mut DirBufferReader) -> Result<usize, Error> {
        warn!("getdents_at is not implemented");
        Err(code::ENOTDIR)
    }
    fn create(
        &self,
        name: &str,
        type_: InodeFileType,
        mode: InodeMode,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        warn!("create is not implemented");
        Err(code::EINVAL)
    }
    fn create_device(
        &self,
        name: &str,
        mode: InodeMode,
        device: Arc<dyn Device>,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        warn!("create_device is not implemented");
        Err(code::EINVAL)
    }
    fn create_socket(&self, mode: InodeMode) -> Result<Arc<dyn InodeOps>, Error> {
        warn!("create_socket is not implemented");
        Err(code::EINVAL)
    }
    fn close(&self) -> Result<(), Error> {
        Ok(())
    }
    fn ioctl(&self, cmd: u32, arg: usize) -> Result<i32, Error> {
        warn!("ioctl is not implemented");
        Err(code::ENOTDIR)
    }
    fn flush(&self) -> Result<(), Error> {
        Ok(())
    }
    fn fsync(&self) -> Result<(), Error> {
        Ok(())
    }
    fn lookup(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        warn!("lookup is not implemented");
        Err(code::ENOTDIR)
    }
    fn resize(&self, size: usize) -> Result<(), Error> {
        warn!("resize is not supported");
        Err(code::EINVAL)
    }
    fn is_dcacheable(&self) -> bool {
        true
    }
    fn fs(&self) -> Option<Arc<dyn FileSystem>>;
    fn ino(&self) -> InodeNo;
    fn type_(&self) -> InodeFileType;
    fn inode_attr(&self) -> InodeAttr;
    fn file_attr(&self) -> FileAttr;
    fn mode(&self) -> InodeMode;
    fn size(&self) -> usize;
    fn atime(&self) -> Duration;
    fn set_atime(&self, time: Duration);
    fn mtime(&self) -> Duration;
    fn set_mtime(&self, time: Duration);
}

impl dyn InodeOps {
    pub fn downcast_ref<T: InodeOps>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref::<T>()
    }
}

impl fmt::Debug for dyn InodeOps {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("InodeOps")
            .field("attr", &self.inode_attr())
            .field("fs", &self.fs())
            .finish()
    }
}
