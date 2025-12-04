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
    error::{code, Error},
    vfs::{
        dcache::Dcache,
        dirent::DirBufferReader,
        fs::FileSystemInfo,
        inode::{InodeAttr, InodeNo},
        inode_mode::{mode_t, InodeFileType},
        utils::SeekFrom,
    },
};
use alloc::sync::Arc;
use core::{
    any::Any,
    sync::atomic::{AtomicI32, Ordering},
    time::Duration,
};
use log::warn;
// TODO: use os mutex
use bitflags::bitflags;
use delegate::delegate;
use spin::Mutex;

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AccessMode {
    /// read only
    O_RDONLY = libc::O_RDONLY as u8,
    /// write only
    O_WRONLY = libc::O_WRONLY as u8,
    /// read write
    O_RDWR = libc::O_RDWR as u8,
}

impl AccessMode {
    pub fn is_readable(&self) -> bool {
        self == &AccessMode::O_RDONLY || self == &AccessMode::O_RDWR
    }

    pub fn is_writable(&self) -> bool {
        self == &AccessMode::O_WRONLY || self == &AccessMode::O_RDWR
    }
}

impl From<AccessMode> for i32 {
    fn from(mode: AccessMode) -> Self {
        mode as i32
    }
}

impl From<i32> for AccessMode {
    fn from(mode: i32) -> Self {
        match mode & libc::O_ACCMODE {
            libc::O_RDONLY => AccessMode::O_RDONLY,
            libc::O_WRONLY => AccessMode::O_WRONLY,
            libc::O_RDWR => AccessMode::O_RDWR,
            _ => unreachable!(),
        }
    }
}

// Some flags are not supported yet
// const O_NOCTTY = libc::O_NOCTTY;
// const O_DSYNC = libc::O_DSYNC;
// const O_ASYNC = libc::O_ASYNC;
// const O_DIRECT = libc::O_DIRECT;
// const O_NOATIME = libc::O_NOATIME;
// const O_PATH = libc::O_PATH;
bitflags! {
    pub struct OpenFlags: i32 {
        const O_CREAT = libc::O_CREAT;
        const O_EXCL = libc::O_EXCL;
        const O_TRUNC = libc::O_TRUNC;
        const O_APPEND = libc::O_APPEND;
        const O_NONBLOCK = libc::O_NONBLOCK;
        const O_NOFOLLOW = libc::O_NOFOLLOW;
        const O_CLOEXEC = libc::O_CLOEXEC;
        const O_DIRECTORY = libc::O_DIRECTORY;
        const O_SYNC = libc::O_SYNC;
    }
}

impl From<i32> for OpenFlags {
    fn from(flags: i32) -> Self {
        let bits = flags & !libc::O_ACCMODE;
        OpenFlags::from_bits_truncate(bits)
    }
}

#[derive(Debug, Clone, Default)]
pub struct FileAttr {
    pub dev: usize,
    pub ino: InodeNo,
    pub size: usize,
    pub blk_size: usize,
    pub blocks: usize,
    pub atime: Duration,
    pub mtime: Duration,
    pub ctime: Duration,
    pub mode: mode_t,
    pub nlinks: u32,
    pub uid: u32,
    pub gid: u32,
    pub rdev: usize,
}

impl FileAttr {
    pub fn new(dev: usize, rdev: usize, inode: &InodeAttr) -> Self {
        Self {
            dev,
            ino: inode.inode_no,
            size: inode.size,
            blk_size: inode.blk_size,
            blocks: inode.blocks,
            atime: inode.atime,
            mtime: inode.mtime,
            ctime: inode.ctime,
            mode: inode.mode,
            nlinks: inode.nlinks,
            uid: inode.uid,
            gid: inode.gid,
            rdev,
        }
    }

    pub fn ino(&self) -> InodeNo {
        self.ino
    }

    pub fn type_(&self) -> InodeFileType {
        InodeFileType::from(self.mode)
    }
}

pub trait FileOps: Send + Sync + Any {
    fn read(&self, buf: &mut [u8]) -> Result<usize, Error> {
        warn!("read is not implemented");
        Err(code::EINVAL)
    }
    fn write(&self, buf: &[u8]) -> Result<usize, Error> {
        warn!("write is not implemented");
        Err(code::EINVAL)
    }
    fn seek(&self, seek_from: SeekFrom) -> Result<usize, Error> {
        warn!("seek is not implemented");
        Err(code::ESPIPE)
    }
    fn ioctl(&self, cmd: u32, arg: usize) -> Result<i32, Error> {
        warn!("ioctl is not implemented");
        Err(code::EINVAL)
    }
    fn flush(&self) -> Result<(), Error> {
        Ok(())
    }
    fn close(&self) -> Result<(), Error> {
        Ok(())
    }
    fn resize(&self, new_size: usize) -> Result<(), Error> {
        warn!("resize is not implemented");
        Err(code::EINVAL)
    }
    fn dup(&self, close_on_exec: bool) -> Result<Arc<dyn FileOps>, Error> {
        warn!("dup is not implemented");
        Err(code::EINVAL)
    }
    fn stat(&self) -> FileAttr;
    fn flags(&self) -> OpenFlags;
    fn set_flags(&self, flags: OpenFlags);
}

// system file hander
#[derive(Debug)]
pub struct File {
    dcache: Arc<Dcache>,
    open_flags: AtomicI32,
    offset: Mutex<usize>, // also lock for read/ write
}

impl File {
    pub fn new(
        dcache: Arc<Dcache>,
        access_mode: AccessMode,
        flags: OpenFlags,
    ) -> Result<Self, Error> {
        let inode = dcache.inode();
        // check inode access mode
        if access_mode.is_readable() && !inode.mode().is_readable() {
            return Err(code::EACCES);
        }
        if access_mode.is_writable() && !inode.mode().is_writable() {
            return Err(code::EACCES);
        }
        if access_mode.is_writable() && inode.type_() == InodeFileType::Directory {
            return Err(code::EISDIR);
        }

        Ok(Self {
            dcache,
            open_flags: AtomicI32::new(access_mode as i32 | flags.bits()),
            offset: Mutex::new(0),
        })
    }

    pub fn dcache(&self) -> Arc<Dcache> {
        self.dcache.clone()
    }

    pub fn access_mode(&self) -> AccessMode {
        let bits = self.open_flags.load(Ordering::Relaxed);
        AccessMode::from(bits)
    }

    pub fn open_flags(&self) -> OpenFlags {
        let bits = self.open_flags.load(Ordering::Relaxed);
        OpenFlags::from(bits)
    }

    pub fn set_open_flags(&self, flags: OpenFlags) {
        let flags = flags.bits() | self.access_mode() as i32;
        self.open_flags.store(flags, Ordering::Relaxed);
    }

    pub fn is_nonblock(&self) -> bool {
        self.open_flags().contains(OpenFlags::O_NONBLOCK)
    }

    pub fn offset(&self) -> usize {
        *self.offset.lock()
    }

    pub fn getdents(&self, reader: &mut DirBufferReader) -> Result<usize, Error> {
        let mut offset = self.offset.lock();
        let cnt = self.dcache.inode().getdents_at(*offset, reader)?;
        *offset += cnt;
        Ok(cnt)
    }

    pub fn fs_info(&self) -> FileSystemInfo {
        self.dcache.fs_info()
    }

    delegate! {
        to self.dcache {
            pub fn type_(&self) -> InodeFileType;
        }
    }
}

impl FileOps for File {
    fn read(&self, buf: &mut [u8]) -> Result<usize, Error> {
        if !self.access_mode().is_readable() {
            return Err(code::EACCES);
        }
        let mut offset = self.offset.lock();
        // TODO: support O_DIRECT
        let ret = self
            .dcache
            .inode()
            .read_at(*offset, buf, self.is_nonblock())?;
        *offset += ret;
        Ok(ret)
    }

    fn write(&self, buf: &[u8]) -> Result<usize, Error> {
        if !self.access_mode().is_writable() {
            return Err(code::EACCES);
        }
        let mut offset = self.offset.lock();
        // offset is ignored if O_APPEND is set
        if self.open_flags().contains(OpenFlags::O_APPEND) {
            *offset = self.dcache.size();
        }
        let ret = self
            .dcache
            .inode()
            .write_at(*offset, buf, self.is_nonblock())?;
        *offset += ret;
        Ok(ret)
    }

    fn seek(&self, pos: SeekFrom) -> Result<usize, Error> {
        let mut cur_offset = self.offset.lock();
        let new_offset: isize = match pos {
            SeekFrom::Start(offset) => {
                if offset > isize::MAX as u64 {
                    return Err(code::EINVAL);
                }
                offset as isize
            }
            SeekFrom::End(offset) => {
                let file_size = self.dcache.size() as isize;
                file_size
                    .checked_add(offset as isize)
                    .ok_or(code::EOVERFLOW)?
            }
            SeekFrom::Current(offset) => (*cur_offset as isize)
                .checked_add(offset as isize)
                .ok_or(code::EOVERFLOW)?,
        };

        debug_assert!(new_offset >= 0);
        *cur_offset = new_offset as usize;
        Ok(new_offset as usize)
    }

    fn ioctl(&self, cmd: u32, arg: usize) -> Result<i32, Error> {
        self.dcache.inode().ioctl(cmd, arg)
    }

    fn flush(&self) -> Result<(), Error> {
        self.dcache.inode().flush()
    }

    fn close(&self) -> Result<(), Error> {
        self.dcache.inode().close()
    }

    fn resize(&self, new_size: usize) -> Result<(), Error> {
        if !self.access_mode().is_writable() {
            return Err(code::EACCES);
        }
        self.dcache.inode().resize(new_size)
    }

    fn dup(&self, close_on_exec: bool) -> Result<Arc<dyn FileOps>, Error> {
        let flags = self.open_flags();
        let flags = if close_on_exec {
            flags | OpenFlags::O_CLOEXEC
        } else {
            flags
        };
        Ok(Arc::new(File::new(
            self.dcache(),
            self.access_mode(),
            flags,
        )?))
    }

    fn stat(&self) -> FileAttr {
        let inode = self.dcache.inode();
        inode.file_attr()
    }

    fn flags(&self) -> OpenFlags {
        self.open_flags()
    }

    fn set_flags(&self, flags: OpenFlags) {
        self.set_open_flags(flags);
    }
}

impl dyn FileOps {
    pub fn downcast_ref<T: FileOps>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref::<T>()
    }
}
