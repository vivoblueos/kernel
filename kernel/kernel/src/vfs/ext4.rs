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

use crate::{
    devices::{Device, DeviceManager},
    error::{code, Error},
    vfs::{
        dcache::Dcache,
        dirent::DirBufferReader,
        file::FileAttr,
        fs::{FileSystem, FileSystemInfo},
        inode::{InodeAttr, InodeNo, InodeOps},
        inode_mode::{InodeFileType, InodeMode},
        tmpfs::TmpFileSystem,
        utils::NAME_MAX,
    },
};
use alloc::sync::{Arc, Weak};
use core::{
    str,
    sync::atomic::{AtomicBool, Ordering},
    time::Duration,
};
use rsext4::{
    BlockIo, DeviceCapabilities, DeviceGeometry, DirectoryCursor, DirectoryEntryType, Ext4,
    Ext4Error, Ext4Result, Ext4Timestamp, FileName, FilePermissions, InodeInfo,
    InodeMetadataUpdate, MountOptions, MountServices, MountedServices, MutationContext,
    NoopObserver, RenameOptions, SectorId,
};
use spin::{Mutex, RwLock};

const EXT4_MAGIC: usize = rsext4::EXT4_SUPER_MAGIC as usize;

type Ext4Core = Ext4<Ext4BlockDevice, MountedServices<(), NoopObserver>>;

struct Ext4Clock;

impl rsext4::Clock for Ext4Clock {
    fn now(&self) -> Ext4Result<Ext4Timestamp> {
        let now = crate::time::now();
        Ok(Ext4Timestamp::new(now.as_secs() as i64, now.subsec_nanos()))
    }
}

struct Ext4BlockDevice {
    device: Arc<dyn Device>,
    sector_size: u32,
    sector_count: u64,
}

impl Ext4BlockDevice {
    fn new(device: Arc<dyn Device>) -> Result<Self, Error> {
        let sector_size = u32::from(device.sector_size().map_err(|_| code::EIO)?);
        let sector_count = device.capacity().map_err(|_| code::EIO)?;
        if sector_size == 0 {
            return Err(code::EINVAL);
        }
        Ok(Self {
            device,
            sector_size,
            sector_count,
        })
    }

    fn byte_offset(&self, sector: SectorId) -> Ext4Result<u64> {
        sector
            .raw()
            .checked_mul(u64::from(self.sector_size))
            .ok_or_else(Ext4Error::overflow)
    }

    fn expected_len(&self, count: u32) -> Ext4Result<usize> {
        usize::try_from(self.sector_size)
            .ok()
            .and_then(|size| size.checked_mul(count as usize))
            .ok_or_else(Ext4Error::overflow)
    }
}

impl BlockIo for Ext4BlockDevice {
    fn write(&mut self, buffer: &[u8], sector: SectorId, count: u32) -> Ext4Result<()> {
        let expected = self.expected_len(count)?;
        if buffer.len() != expected {
            return Err(Ext4Error::invalid_block_size(buffer.len(), expected));
        }
        let written = self
            .device
            .write(self.byte_offset(sector)?, buffer, false)
            .map_err(|_| Ext4Error::io())?;
        if written != expected {
            return Err(Ext4Error::io());
        }
        Ok(())
    }

    fn read(&mut self, buffer: &mut [u8], sector: SectorId, count: u32) -> Ext4Result<()> {
        let expected = self.expected_len(count)?;
        if buffer.len() != expected {
            return Err(Ext4Error::invalid_block_size(buffer.len(), expected));
        }
        let read = self
            .device
            .read(self.byte_offset(sector)?, buffer, false)
            .map_err(|_| Ext4Error::io())?;
        if read != expected {
            return Err(Ext4Error::io());
        }
        Ok(())
    }

    fn geometry(&self) -> DeviceGeometry {
        DeviceGeometry::new(self.sector_size, self.sector_count)
    }

    fn capabilities(&self) -> DeviceCapabilities {
        DeviceCapabilities {
            flush: true,
            ..DeviceCapabilities::default()
        }
    }

    fn flush(&mut self) -> Ext4Result<()> {
        self.device.sync().map_err(|_| Ext4Error::io())
    }
}

pub struct Ext4FileSystem {
    core: Mutex<Ext4Core>,
    root: Arc<Ext4Inode>,
    anonymous: Arc<TmpFileSystem>,
    mounted: AtomicBool,
}

impl Ext4FileSystem {
    pub fn new(device_name: &str) -> Result<Arc<Self>, Error> {
        let device = DeviceManager::get()
            .get_block_device(device_name)
            .ok_or(code::ENODEV)?;
        let device = Ext4BlockDevice::new(device)?;
        let services = MountServices::new(Ext4Clock, (), NoopObserver);
        let mut core = Ext4::mount(device, services, MountOptions::read_write())?;
        let root_info = core.inode(core.root_inode())?;

        Ok(Arc::new_cyclic(move |weak_fs| Self {
            core: Mutex::new(core),
            root: Ext4Inode::new_root(weak_fs.clone(), root_info),
            anonymous: TmpFileSystem::new(),
            mounted: AtomicBool::new(true),
        }))
    }

    fn check_mounted(&self) -> Result<(), Error> {
        if self.mounted.load(Ordering::Acquire) {
            Ok(())
        } else {
            Err(code::EINVAL)
        }
    }
}

impl FileSystem for Ext4FileSystem {
    fn mount(&self, _mount_point: Arc<Dcache>) -> Result<(), Error> {
        if self.mounted.swap(true, Ordering::AcqRel) {
            return Err(code::EBUSY);
        }
        Ok(())
    }

    fn unmount(&self) -> Result<(), Error> {
        self.check_mounted()?;
        self.core.lock().unmount()?;
        self.mounted.store(false, Ordering::Release);
        Ok(())
    }

    fn sync(&self) -> Result<(), Error> {
        self.check_mounted()?;
        self.core.lock().sync().map_err(Into::into)
    }

    fn root_inode(&self) -> Arc<dyn InodeOps> {
        self.root.clone()
    }

    fn fs_info(&self) -> FileSystemInfo {
        let stats = self.core.lock().statfs();
        FileSystemInfo {
            magic: EXT4_MAGIC,
            dev: 0,
            namelen: NAME_MAX,
            bsize: stats.block_size as usize,
            frsize: stats.block_size as usize,
            blocks: stats.total_blocks as usize,
            bfree: stats.free_blocks as usize,
            bavail: stats.free_blocks as usize,
            files: stats.total_inodes as usize,
            ffree: stats.free_inodes as usize,
            favail: stats.free_inodes as usize,
            ..FileSystemInfo::default()
        }
    }

    fn fs_type(&self) -> &str {
        "ext4"
    }
}

struct Ext4Inode {
    number: rsext4::InodeNumber,
    info: RwLock<InodeInfo>,
    this: Weak<Ext4Inode>,
    parent: Weak<Ext4Inode>,
    fs: Weak<Ext4FileSystem>,
}

impl Ext4Inode {
    fn new_root(fs: Weak<Ext4FileSystem>, info: InodeInfo) -> Arc<Self> {
        Arc::new_cyclic(|this| Self {
            number: info.number,
            info: RwLock::new(info),
            this: this.clone(),
            parent: this.clone(),
            fs,
        })
    }

    fn new(fs: &Weak<Ext4FileSystem>, parent: &Weak<Ext4Inode>, info: InodeInfo) -> Arc<Self> {
        Arc::new_cyclic(|this| Self {
            number: info.number,
            info: RwLock::new(info),
            this: this.clone(),
            parent: parent.clone(),
            fs: fs.clone(),
        })
    }

    fn filesystem(&self) -> Result<Arc<Ext4FileSystem>, Error> {
        self.fs.upgrade().ok_or(code::EIO)
    }

    fn file_name<'a>(name: &'a str) -> Result<FileName<'a>, Error> {
        FileName::new(name.as_bytes()).map_err(Into::into)
    }

    fn permissions(mode: InodeMode) -> Result<FilePermissions, Error> {
        FilePermissions::new((mode.bits() & 0o7777) as u16).map_err(Into::into)
    }

    fn child(&self, info: InodeInfo) -> Arc<Ext4Inode> {
        Ext4Inode::new(&self.fs, &self.this, info)
    }

    fn update_info(&self, info: InodeInfo) {
        *self.info.write() = info;
    }

    fn info_to_attr(info: InodeInfo, block_size: usize) -> InodeAttr {
        InodeAttr {
            inode_no: info.number.raw() as usize,
            size: info.size as usize,
            blk_size: block_size,
            blocks: info.blocks as usize,
            atime: Duration::from_secs(info.atime as u64),
            mtime: Duration::from_secs(info.mtime as u64),
            ctime: Duration::from_secs(info.ctime as u64),
            mode: u32::from(info.mode),
            nlinks: u32::from(info.links),
            uid: info.uid,
            gid: info.gid,
        }
    }

    fn entry_type(type_: DirectoryEntryType) -> InodeFileType {
        match type_ {
            DirectoryEntryType::RegularFile => InodeFileType::Regular,
            DirectoryEntryType::Directory => InodeFileType::Directory,
            DirectoryEntryType::CharacterDevice => InodeFileType::CharDevice,
            DirectoryEntryType::BlockDevice => InodeFileType::BlockDevice,
            DirectoryEntryType::Fifo => InodeFileType::Fifo,
            DirectoryEntryType::Socket => InodeFileType::Socket,
            DirectoryEntryType::Symlink => InodeFileType::SymLink,
            DirectoryEntryType::Unknown => InodeFileType::Unknown,
        }
    }

    fn mutate_time(&self, atime: Option<Duration>, mtime: Option<Duration>) {
        let Ok(fs) = self.filesystem() else {
            return;
        };
        let update = InodeMetadataUpdate {
            atime: atime.map(|time| Ext4Timestamp::new(time.as_secs() as i64, time.subsec_nanos())),
            mtime: mtime.map(|time| Ext4Timestamp::new(time.as_secs() as i64, time.subsec_nanos())),
            ..InodeMetadataUpdate::default()
        };
        if let Ok(info) = fs.core.lock().update_inode_metadata(self.number, update) {
            self.update_info(info);
        }
    }
}

impl InodeOps for Ext4Inode {
    fn read_at(&self, offset: usize, buf: &mut [u8], _nonblock: bool) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Regular {
            return Err(code::EISDIR);
        }
        self.filesystem()?
            .core
            .lock()
            .read_inode(self.number, offset as u64, buf)
            .map_err(Into::into)
    }

    fn write_at(&self, offset: usize, buf: &[u8], _nonblock: bool) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Regular {
            return Err(code::EISDIR);
        }
        let fs = self.filesystem()?;
        {
            let mut core = fs.core.lock();
            core.write_inode(self.number, offset as u64, buf)?;
            self.update_info(core.inode(self.number)?);
        }
        Ok(buf.len())
    }

    fn lookup(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        if self.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        if name == "." {
            return self
                .this
                .upgrade()
                .map(|inode| inode as Arc<dyn InodeOps>)
                .ok_or(code::EIO);
        }
        if name == ".." {
            return self
                .parent
                .upgrade()
                .map(|inode| inode as Arc<dyn InodeOps>)
                .ok_or(code::EIO);
        }
        let fs = self.filesystem()?;
        let info = fs
            .core
            .lock()
            .lookup_child(self.number, Self::file_name(name)?)?
            .ok_or(code::ENOENT)?;
        Ok(self.child(info))
    }

    fn getdents_at(&self, offset: usize, reader: &mut DirBufferReader) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let fs = self.filesystem()?;
        let entries = fs.core.lock().read_directory(
            self.number,
            DirectoryCursor::Start,
            offset.saturating_add(64),
        )?;
        let mut count = 0;
        for (index, entry) in entries.into_iter().enumerate().skip(offset) {
            let name = str::from_utf8(&entry.name).map_err(|_| code::EILSEQ)?;
            match reader.write_node(
                entry.inode.raw() as usize,
                index as i64,
                Self::entry_type(entry.file_type),
                name,
            ) {
                Ok(()) => count += 1,
                Err(_error) if count != 0 => return Ok(count),
                Err(error) => return Err(error),
            }
        }
        Ok(count)
    }

    fn create(
        &self,
        name: &str,
        type_: InodeFileType,
        mode: InodeMode,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        if self.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let fs = self.filesystem()?;
        let mut core = fs.core.lock();
        let context = MutationContext::new(0, 0, 0, 0);
        let name = Self::file_name(name)?;
        let permissions = Self::permissions(mode)?;
        let info = match type_ {
            InodeFileType::Regular => {
                core.create_regular_file(context, self.number, name, permissions)?
            }
            InodeFileType::Directory => {
                core.create_directory(context, self.number, name, permissions)?
            }
            _ => return Err(code::ENOTSUP),
        };
        Ok(self.child(info))
    }

    fn create_socket(&self, mode: InodeMode) -> Result<Arc<dyn InodeOps>, Error> {
        self.filesystem()?
            .anonymous
            .root_inode()
            .create_socket(mode)
    }

    fn link(&self, old: &Arc<dyn InodeOps>, name: &str) -> Result<(), Error> {
        let old = old.downcast_ref::<Ext4Inode>().ok_or(code::EXDEV)?;
        let fs = self.filesystem()?;
        let old_fs = old.filesystem()?;
        if !Arc::ptr_eq(&fs, &old_fs) {
            return Err(code::EXDEV);
        }
        fs.core
            .lock()
            .hard_link(old.number, self.number, Self::file_name(name)?)?;
        Ok(())
    }

    fn unlink(&self, name: &str) -> Result<(), Error> {
        let outcome = self
            .filesystem()?
            .core
            .lock()
            .unlink(self.number, Self::file_name(name)?)?;
        if outcome.requires_reap() {
            // Reaping must wait for the final VFS inode reference. BlueKernel
            // currently has no inode-release callback, so journal recovery owns
            // final reclamation after a reboot instead of invalidating open files.
        }
        Ok(())
    }

    fn rmdir(&self, name: &str) -> Result<(), Error> {
        let outcome = self
            .filesystem()?
            .core
            .lock()
            .remove_empty_directory(self.number, Self::file_name(name)?)?;
        if outcome.requires_reap() {
            // See unlink(): defer physical inode reclamation.
        }
        Ok(())
    }

    fn rename(
        &self,
        old_name: &str,
        target: &Arc<dyn InodeOps>,
        new_name: &str,
    ) -> Result<(), Error> {
        let target = target.downcast_ref::<Ext4Inode>().ok_or(code::EXDEV)?;
        let fs = self.filesystem()?;
        let target_fs = target.filesystem()?;
        if !Arc::ptr_eq(&fs, &target_fs) {
            return Err(code::EXDEV);
        }
        fs.core.lock().rename(
            self.number,
            Self::file_name(old_name)?,
            target.number,
            Self::file_name(new_name)?,
            RenameOptions::REPLACE,
        )?;
        Ok(())
    }

    fn resize(&self, size: usize) -> Result<(), Error> {
        let fs = self.filesystem()?;
        let mut core = fs.core.lock();
        core.truncate_inode(self.number, size as u64)?;
        self.update_info(core.inode(self.number)?);
        Ok(())
    }

    fn flush(&self) -> Result<(), Error> {
        self.fsync()
    }

    fn fsync(&self) -> Result<(), Error> {
        self.filesystem()?.sync()
    }

    fn fs(&self) -> Option<Arc<dyn FileSystem>> {
        self.fs.upgrade().map(|fs| fs as Arc<dyn FileSystem>)
    }

    fn ino(&self) -> InodeNo {
        self.number.raw() as usize
    }

    fn type_(&self) -> InodeFileType {
        Self::entry_type(self.info.read().file_type())
    }

    fn inode_attr(&self) -> InodeAttr {
        let block_size = self
            .fs
            .upgrade()
            .map(|fs| fs.fs_info().bsize)
            .unwrap_or_default();
        Self::info_to_attr(*self.info.read(), block_size)
    }

    fn file_attr(&self) -> FileAttr {
        FileAttr::new(0, 0, &self.inode_attr())
    }

    fn mode(&self) -> InodeMode {
        InodeMode::from(u32::from(self.info.read().mode))
    }

    fn size(&self) -> usize {
        self.info.read().size as usize
    }

    fn atime(&self) -> Duration {
        Duration::from_secs(self.info.read().atime as u64)
    }

    fn set_atime(&self, time: Duration) {
        self.mutate_time(Some(time), None);
    }

    fn mtime(&self) -> Duration {
        Duration::from_secs(self.info.read().mtime as u64)
    }

    fn set_mtime(&self, time: Duration) {
        self.mutate_time(None, Some(time));
    }
}
