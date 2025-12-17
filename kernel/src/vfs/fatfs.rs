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
    devices::{Device, DeviceManager},
    error::{code, Error},
    vfs::{
        dcache::Dcache,
        dirent::DirBufferReader,
        file::FileAttr,
        fs::{FileSystem, FileSystemInfo},
        inode::{InodeAttr, InodeNo, InodeOps},
        inode_mode::{InodeFileType, InodeMode},
        utils::NAME_MAX,
    },
};
use alloc::{
    boxed::Box,
    collections::BTreeMap,
    string::String,
    sync::{Arc, Weak},
};
use core::{
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    time::Duration,
};
use delegate::delegate;
use embedded_io::ErrorKind;
use fatfs::{DefaultTimeProvider, IoBase, LossyOemCpConverter, Read, Seek, SeekFrom, Write};
use log::{debug, error, info, trace, warn};
use spin::{mutex::Mutex, MutexGuard, RwLock};

static MAGIC: usize = 0x16914836;
const ROOT_INO: InodeNo = 1;
const BLOCK_SIZE: u32 = 4096;
const TYPE_FAT_12: &str = "Fat12";
const TYPE_FAT_16: &str = "Fat16";
const TYPE_FAT_32: &str = "Fat32";

use core::{cell::UnsafeCell, mem::MaybeUninit};

type Dir = fatfs::Dir<'static, FatStorage, DefaultTimeProvider, LossyOemCpConverter>;
type File = fatfs::File<'static, FatStorage, DefaultTimeProvider, LossyOemCpConverter>;

pub static NEXT_INODE_NO: AtomicUsize = AtomicUsize::new(ROOT_INO + 1);

// A Fat file system based on fatfs::FileSystem
pub struct FatFileSystem {
    root: Arc<FatInode>,
    fs_info: FileSystemInfo,
    is_mounted: AtomicBool,
    fat_type: &'static str,
    next_inode_no: AtomicUsize,
    device_name: String,
}

// SAFETY: fatfs::FileSystem/Dir/File is not thread-safe, but we use a global lock to ensure safety when calling its function
unsafe impl Send for FatFileSystem {}
unsafe impl Sync for FatFileSystem {}
unsafe impl Send for FatInode {}
unsafe impl Sync for FatInode {}
unsafe impl Sync for InternalFsWrapper {}

impl FatFileSystem {
    /// Allocate new inode number
    #[inline(always)]
    pub fn alloc_inode_no(&self) -> InodeNo {
        self.next_inode_no.fetch_add(1, Ordering::Relaxed)
    }

    pub fn new(device_name: &str) -> Result<Arc<Self>, Error> {
        if INTERNAL_FS_INSTANCES.read().contains_key(device_name) {
            error!("[FatFileSystem] A file system on the same device already exists.");
            return Err(code::EAGAIN);
        }

        let mut storage = FatStorage::new(device_name)?;
        let format_opts = fatfs::FormatVolumeOptions::new()
            .bytes_per_sector(storage.sector_size)
            .total_sectors(storage.sector_num.try_into().unwrap())
            .bytes_per_cluster(BLOCK_SIZE);
        let internal_fs = Box::new({
            match fatfs::FileSystem::new(storage.clone(), fatfs::FsOptions::new()) {
                Ok(fs) => fs,
                Err(_) => {
                    warn!(
                        "[FatFileSystem] Faild to construct internal fs, format it and try again."
                    );
                    fatfs::format_volume(&mut storage, format_opts)
                        .expect("[FatFileSystem] Format volume fail.");
                    fatfs::FileSystem::new(storage, fatfs::FsOptions::new())
                        .expect("[FatFileSystem] Faild to construct internal fs again")
                }
            }
        });
        let wrapper = Box::new(InternalFsWrapper {
            fs: Box::leak(internal_fs),
            lock: Arc::new(Mutex::new(())),
        });
        let internal_fs_wrapper: &'static InternalFsWrapper = Box::leak(wrapper);
        let (internal_fs, _) = internal_fs_wrapper.get();
        let cluster_size = internal_fs.cluster_size();
        let total_clusters = internal_fs.total_clusters();
        let fat_type = internal_fs.fat_type();
        info!(
            "[FatFileSystem] internal fs created, type {:?}, cluster size {}, total_clusters {}",
            fat_type, cluster_size, total_clusters,
        );
        debug_assert!(cluster_size == BLOCK_SIZE);
        let fs_info = FileSystemInfo::new(
            MAGIC,
            0,
            NAME_MAX,
            cluster_size.try_into().unwrap(),
            total_clusters.try_into().unwrap(),
        );
        let fs = Arc::new_cyclic(|weak_fs| {
            let root_dir = internal_fs.root_dir();
            let root_node = Arc::new_cyclic(|weak_root| {
                let attr = InodeAttr::new(
                    ROOT_INO,
                    InodeFileType::Directory,
                    InodeMode::from_bits_truncate(0o755),
                    0,
                    0,
                    BLOCK_SIZE.try_into().unwrap(),
                );
                FatInode {
                    inner: RwLock::new(InnerNode {
                        attr,
                        data: FatFileData::Directory(FatDir::new(
                            weak_root,
                            internal_fs_wrapper.wrap(root_dir),
                        )),
                    }),
                    this: weak_root.clone(),
                    fs: weak_fs.clone(),
                }
            });
            Self {
                root: root_node,
                is_mounted: AtomicBool::new(false),
                fs_info,
                fat_type: match fat_type {
                    fatfs::FatType::Fat12 => TYPE_FAT_12,
                    fatfs::FatType::Fat16 => TYPE_FAT_16,
                    fatfs::FatType::Fat32 => TYPE_FAT_32,
                },
                next_inode_no: AtomicUsize::new(ROOT_INO),
                device_name: String::from(device_name),
            }
        });
        INTERNAL_FS_INSTANCES
            .write()
            .insert(String::from(device_name), internal_fs_wrapper);
        Ok(fs)
    }

    fn check_mounted(&self) -> bool {
        self.is_mounted.load(Ordering::Relaxed)
    }

    fn build_dcache(&self, dir: Dir, dcache: Arc<Dcache>) -> Result<(), Error> {
        debug!(
            "[FatFileSystem] build_dcache for {}",
            dcache.get_full_path()
        );
        let parent_inode: &FatInode = dcache.inode().downcast_ref::<FatInode>().unwrap();
        for r in dir.iter() {
            let e = r.unwrap();
            let name = e.file_name();
            // ignore special entries "." and ".."
            if &name == "." || &name == ".." {
                continue;
            }
            debug!("[FatFileSystem] build_dcache: Find a entry {}", name);
            let inode = if e.is_dir() {
                // Use defalut permission 0o755 for dir
                let mode = InodeMode::from(0o755);
                let child_dir = e.to_dir();
                let inode = FatInode::new_dir(
                    &name,
                    &parent_inode.fs,
                    self.alloc_inode_no(),
                    mode,
                    0,
                    0,
                    &parent_inode.this,
                    child_dir.clone(),
                )?;
                let inode_clone: Arc<dyn InodeOps> = inode.clone();
                let child_dcache = dcache.new_child(
                    &name,
                    InodeFileType::Directory,
                    InodeMode::from(0o755),
                    move || Some(inode_clone),
                )?;
                self.build_dcache(child_dir, child_dcache)?;
                inode
            } else if e.is_file() {
                // Use defalut permission 0o644 for regular file
                let mode: InodeMode = InodeMode::from(0o644);
                let child_file = e.to_file();
                let inode = FatInode::new_file(
                    &name,
                    &parent_inode.fs,
                    self.alloc_inode_no(),
                    mode,
                    0,
                    0,
                    &parent_inode.this,
                    child_file,
                )?;
                let inode_clone: Arc<dyn InodeOps> = inode.clone();
                let _ = dcache.new_child(
                    &name,
                    InodeFileType::Directory,
                    InodeMode::from(0o755),
                    move || Some(inode_clone),
                )?;
                inode
            } else {
                error!("[FatFileSystem] build_dcache: Unkonwn entry type.");
                return Err(code::ENOTSUP);
            };
            {
                let mut inner = parent_inode.inner.write();
                let parent_dir: &mut FatDir = inner.as_dir_mut().unwrap();
                parent_dir.insert(&name, &inode);
            }
        }
        Ok(())
    }

    pub fn build_root_dcache(&self, root_dcache: Arc<Dcache>) -> Result<(), Error> {
        // Build the dcache tree based on the data stored on disk
        let (internal_fs, guard) = get_internal_fs_with_guard(&self.device_name);
        let root_dir = internal_fs.root_dir();
        drop(guard);
        debug!("[FatFileSystem] build FatInode tree start");
        self.build_dcache(root_dir, root_dcache)?;
        debug!("[FatFileSystem] build FatInode tree end");
        Ok(())
    }
}

impl FileSystem for FatFileSystem {
    fn mount(&self, mount_point: Arc<Dcache>) -> Result<(), Error> {
        if self.check_mounted() {
            error!("[FatFileSystem] mount: already mounted");
            return Err(code::EBUSY);
        }
        self.build_root_dcache(mount_point.clone())?;
        self.is_mounted.store(true, Ordering::Relaxed);
        Ok(())
    }

    fn unmount(&self) -> Result<(), Error> {
        debug!("[FatFileSystem] unmount");
        if !self.check_mounted() {
            return Err(code::EINVAL);
        }
        self.is_mounted.store(false, Ordering::Relaxed);
        Ok(())
    }

    fn sync(&self) -> Result<(), Error> {
        let (internal_fs, _) = get_internal_fs_with_guard(&self.device_name);
        internal_fs.flush_fs_info()?;
        Ok(())
    }

    fn root_inode(&self) -> Arc<dyn InodeOps> {
        self.root.clone()
    }

    fn fs_info(&self) -> FileSystemInfo {
        self.fs_info.clone()
    }

    fn fs_type(&self) -> &str {
        self.fat_type
    }
}

impl Drop for FatFileSystem {
    fn drop(&mut self) {
        trace!("[FatFileSystem] drop");
        let internal_fs = INTERNAL_FS_INSTANCES.write().remove(&self.device_name);
        if let Some(internal_fs) = internal_fs {
            let internal_fs =
                unsafe { Box::from_raw(internal_fs as *const _ as *mut InternalFsWrapper) };
            drop(internal_fs);
        }
    }
}

enum FatFileData {
    Directory(FatDir),
    File(FatFile),
}

struct FatFile {
    _parent: Weak<FatInode>,
    internal_file: InternalFsLock<File>,
}

impl FatFile {
    fn new(parent: &Weak<FatInode>, internal_file: InternalFsLock<File>) -> Self {
        Self {
            _parent: parent.clone(),
            internal_file,
        }
    }
}

struct FatDir {
    parent: Weak<FatInode>,
    children: BTreeMap<String, Arc<FatInode>>,
    internal_dir: InternalFsLock<Dir>,
}

impl FatDir {
    fn new(parent: &Weak<FatInode>, internal_dir: InternalFsLock<Dir>) -> Self {
        Self {
            parent: parent.clone(),
            children: BTreeMap::new(),
            internal_dir,
        }
    }

    fn find(&self, name: &str) -> Option<Arc<FatInode>> {
        self.children.get(name).cloned()
    }

    fn insert(&mut self, name: &str, inode: &Arc<FatInode>) {
        self.children.insert(String::from(name), inode.clone());
    }

    fn remove(&mut self, name: &str) {
        self.children.remove(name);
    }
}

/// Inode in fat filesystem
struct FatInode {
    inner: RwLock<InnerNode>,
    this: Weak<FatInode>,
    // fs is hold by mount point, so we use weak reference here
    fs: Weak<FatFileSystem>,
}

impl FatInode {
    fn new_file(
        name: &str,
        fs: &Weak<FatFileSystem>,
        inode_no: InodeNo,
        mode: InodeMode,
        uid: u32,
        gid: u32,
        parent: &Weak<FatInode>,
        internal_file: File,
    ) -> Result<Arc<Self>, Error> {
        let internal_fs_wrapper: &'static InternalFsWrapper = INTERNAL_FS_INSTANCES
            .read()
            .get(&fs.clone().upgrade().unwrap().device_name)
            .unwrap();
        Ok(Arc::new_cyclic(|weak_inode| {
            let mut attr = InodeAttr::new(
                inode_no,
                InodeFileType::Regular,
                mode,
                uid,
                gid,
                BLOCK_SIZE.try_into().unwrap(),
            );
            attr.set_size(internal_file.size().unwrap().try_into().unwrap());
            Self {
                inner: RwLock::new(InnerNode {
                    attr,
                    data: FatFileData::File(FatFile::new(
                        parent,
                        internal_fs_wrapper.wrap(internal_file),
                    )),
                }),
                this: weak_inode.clone(),
                fs: fs.clone(),
            }
        }))
    }

    fn new_dir(
        name: &str,
        fs: &Weak<FatFileSystem>,
        inode_no: InodeNo,
        mode: InodeMode,
        uid: u32,
        gid: u32,
        parent: &Weak<FatInode>,
        internal_dir: Dir,
    ) -> Result<Arc<Self>, Error> {
        let internal_fs_wrapper: &'static InternalFsWrapper = INTERNAL_FS_INSTANCES
            .read()
            .get(&fs.clone().upgrade().unwrap().device_name)
            .unwrap();
        Ok(Arc::new_cyclic(|weak_inode| Self {
            inner: RwLock::new(InnerNode {
                attr: InodeAttr::new(
                    inode_no,
                    InodeFileType::Directory,
                    mode,
                    uid,
                    gid,
                    BLOCK_SIZE.try_into().unwrap(),
                ),
                data: FatFileData::Directory(FatDir::new(
                    parent,
                    internal_fs_wrapper.wrap(internal_dir),
                )),
            }),
            this: weak_inode.clone(),
            fs: fs.clone(),
        }))
    }
}

struct InnerNode {
    attr: InodeAttr,
    data: FatFileData,
}

impl InnerNode {
    fn as_dir(&self) -> Option<&FatDir> {
        match &self.data {
            FatFileData::Directory(dir) => Some(dir),
            _ => None,
        }
    }

    fn as_dir_mut(&mut self) -> Option<&mut FatDir> {
        match &mut self.data {
            FatFileData::Directory(dir) => Some(dir),
            _ => None,
        }
    }

    fn as_file(&self) -> Option<&FatFile> {
        match &self.data {
            FatFileData::File(file) => Some(file),
            _ => None,
        }
    }

    fn as_file_mut(&mut self) -> Option<&mut FatFile> {
        match &mut self.data {
            FatFileData::File(file) => Some(file),
            _ => None,
        }
    }
}

impl InodeOps for FatInode {
    fn create(
        &self,
        name: &str,
        type_: InodeFileType,
        mode: InodeMode,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        trace!(
            "[FatInode] create: name {}, type_ {:?}, mode {:b}",
            name,
            type_,
            mode.bits()
        );
        debug_assert!(self.type_() == InodeFileType::Directory);
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }
        if name == "." || name == ".." {
            return Err(code::EEXIST);
        }

        let mut inner = self.inner.write();
        let dir: &mut FatDir = inner.as_dir_mut().unwrap();
        if dir.find(name).is_some() {
            return Err(code::EEXIST);
        }
        let inode = {
            let (internal_dir, _) = dir.internal_dir.get();
            match type_ {
                InodeFileType::Directory => {
                    // Check: The dir should not exist
                    debug_assert!(!internal_dir.contais_entry(name, true).unwrap());
                    let internal_dir = internal_dir.create_dir(name)?;
                    FatInode::new_dir(
                        name,
                        &self.fs,
                        self.fs.upgrade().unwrap().alloc_inode_no(),
                        mode,
                        0,
                        0,
                        &self.this,
                        internal_dir,
                    )?
                }
                InodeFileType::Regular => {
                    // Check: The file should not exist
                    debug_assert!(!internal_dir.contais_entry(name, false).unwrap());
                    let internal_file = internal_dir.create_file(name)?;
                    FatInode::new_file(
                        name,
                        &self.fs,
                        self.fs.upgrade().unwrap().alloc_inode_no(),
                        mode,
                        0,
                        0,
                        &self.this,
                        internal_file,
                    )?
                }
                _ => {
                    error!("[FatInode] create: unsupported file type: {:?}", type_);
                    return Err(code::EINVAL);
                }
            }
        };
        dir.insert(name, &inode);
        Ok(inode)
    }

    fn close(&self) -> Result<(), Error> {
        Ok(())
    }

    fn read_at(&self, offset: usize, buf: &mut [u8], _nonblock: bool) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Regular {
            error!("[FatInode] read_at: inode is not a file");
            return Err(code::ENOTSUP);
        }
        #[cfg(debug)]
        {
            let inner = self.inner.read();
            let (file, _) = inner.as_file().unwrap().internal_file.get();
            assert_eq!(file.size().unwrap(), inner.attr.size.try_into().unwrap());
        }
        let mut inner = self.inner.write();
        let (file, _) = inner.as_file_mut().unwrap().internal_file.get_mut();
        let expected_read_size = buf.len();
        let mut offset = offset;
        let mut total_read_size = 0;
        let mut buf = buf;
        while expected_read_size > total_read_size {
            file.seek(SeekFrom::Start(offset as u64))?;
            let read_size = file.read(buf)?;
            if read_size == 0 {
                break;
            }
            buf = &mut buf[read_size..];
            offset += read_size;
            total_read_size += read_size;
        }
        Ok(total_read_size)
    }

    // TODO: support nonblock
    fn write_at(&self, offset: usize, buf: &[u8], _nonblock: bool) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Regular {
            error!("[FatInode] write_at: inode is not a file");
            return Err(code::ENOTSUP);
        }
        let (write_size, new_size, extents) = {
            let mut inner = self.inner.write();
            let (file, _) = inner.as_file_mut().unwrap().internal_file.get_mut();
            let mut offset = offset;
            let mut total_write_size = 0;
            let expected_write_size = buf.len();
            let mut buf = buf;
            while expected_write_size > total_write_size {
                file.seek(SeekFrom::Start(offset as u64))?;
                let write_size = file.write(buf)?;
                if write_size == 0 {
                    break;
                }
                buf = &buf[write_size..];
                offset += write_size;
                total_write_size += write_size;
            }
            let new_size = file.size().unwrap() as usize;
            let extents = file.extents().count();
            (total_write_size, new_size, extents)
        };
        {
            // update attr size
            let mut inner = self.inner.write();
            let block_size = inner.attr.blk_size;
            inner.attr.size = new_size;
            inner.attr.blocks = inner.attr.size.div_ceil(block_size);
            debug_assert!(extents == inner.attr.blocks);
        }

        Ok(write_size)
    }

    fn link(&self, _old: &Arc<dyn InodeOps>, _name: &str) -> Result<(), Error> {
        // FAT file system does not support hard link.
        Err(code::ENOTSUP)
    }

    fn unlink(&self, name: &str) -> Result<(), Error> {
        // FAT file system does not support hard link. Here we just delete a simple file.
        if self.type_() != InodeFileType::Directory {
            error!("[FatInode] unlink: not a directory");
            return Err(code::ENOTDIR);
        }
        if name == "." || name == ".." {
            return Err(code::EISDIR);
        }
        let mut inner = self.inner.write();
        let dir: &mut FatDir = inner.as_dir_mut().unwrap();
        let inode = dir.find(name).ok_or(code::ENOENT)?;
        let target = inode.inner.read();
        if target.attr.type_() == InodeFileType::Directory {
            error!("[FatInode] unlink: cannot unlink directory");
            return Err(code::EPERM);
        }
        {
            let (internal_dir, _) = dir.internal_dir.get();
            internal_dir.remove(name)?;
        }
        dir.remove(name);
        Ok(())
    }

    fn rmdir(&self, name: &str) -> Result<(), Error> {
        if name == "." || name == ".." {
            error!("[FatInode] rmdir: cannot remove {}", name);
            return Err(code::EINVAL);
        }
        if self.type_() != InodeFileType::Directory {
            warn!("[FatInode] rmdir: not a directory");
            return Err(code::ENOTDIR);
        }
        let mut inner = self.inner.write();
        let dir: &mut FatDir = inner.as_dir_mut().unwrap();
        let inode = dir.find(name).ok_or(code::ENOENT)?;
        let target = inode.inner.write();
        if target.attr.type_() != InodeFileType::Directory {
            error!("[FatInode] rmdir: target is not a directory");
            return Err(code::ENOTDIR);
        }
        {
            let (internal_dir, _) = dir.internal_dir.get();
            internal_dir.remove(name)?;
        }
        dir.remove(name);
        Ok(())
    }

    fn getdents_at(&self, offset: usize, reader: &mut DirBufferReader) -> Result<usize, Error> {
        if self.type_() != InodeFileType::Directory {
            error!("[FatInode] getdents_at: not a directory");
            return Err(code::ENOTDIR);
        }
        let inner = self.inner.read();
        let dir: &FatDir = inner.as_dir().unwrap();
        let mut count = 0;
        let mut current_offset = offset;

        // Handle special entries (., ..)
        if current_offset == 0 {
            match reader.write_node(
                inner.attr.ino(),
                current_offset as i64,
                inner.attr.type_(),
                ".",
            ) {
                Ok(_) => {
                    count += 1;
                    current_offset += 1;
                }
                Err(e) => return Err(e),
            }
        }
        if current_offset == 1 {
            if let Err(e) = reader.write_node(
                inner.attr.ino(),
                current_offset as i64,
                inner.attr.type_(),
                "..",
            ) {
                if count == 0 {
                    return Err(e);
                }
                return Ok(count);
            }
            count += 1;
            current_offset += 1;
        }
        let start_idx = current_offset.saturating_sub(2);
        for (name, inode) in dir.children.iter().skip(start_idx) {
            match reader.write_node(
                inode.inode_attr().ino(),
                current_offset as i64,
                inode.inode_attr().type_(),
                name,
            ) {
                Ok(_) => {
                    count += 1;
                    current_offset += 1;
                }
                Err(e) => {
                    if count == 0 {
                        return Err(e);
                    }
                    return Ok(count);
                }
            }
        }
        Ok(count)
    }

    fn resize(&self, size: usize) -> Result<(), Error> {
        if self.type_() != InodeFileType::Regular {
            error!("[FatInode] resize: not a file");
            return Err(code::ENOTSUP);
        }
        let (new_size, extents) = {
            let mut inner = self.inner.write();
            let (file, _) = inner.as_file_mut().unwrap().internal_file.get_mut();
            file.seek(SeekFrom::Start(size as u64))?;
            file.truncate()?;
            let new_size = file.size().unwrap() as usize;
            let extents = file.extents().count();
            (new_size, extents)
        };
        {
            // update attr size
            let mut inner = self.inner.write();
            inner.attr.size = new_size;
            let block_size = inner.attr.blk_size;
            inner.attr.blocks = inner.attr.size.div_ceil(block_size);
            debug_assert!(extents == inner.attr.blocks);
        }
        Ok(())
    }

    fn inode_attr(&self) -> InodeAttr {
        self.inner.read().attr.clone()
    }

    fn lookup(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        if self.type_() != InodeFileType::Directory {
            error!("[FatInode] lookup: not a directory");
            return Err(code::ENOTDIR);
        }
        let inner = self.inner.read();
        if name == "." {
            return Ok(self.this.upgrade().unwrap());
        }
        let dir: &FatDir = inner.as_dir().unwrap();
        if name == ".." {
            return Ok(dir.parent.upgrade().unwrap());
        }
        let inode = dir.find(name).ok_or(code::ENOENT)?;
        Ok(inode)
    }

    fn fs(&self) -> Option<Arc<dyn FileSystem>> {
        match self.fs.upgrade() {
            Some(fs) => Some(fs),
            None => None,
        }
    }

    fn flush(&self) -> Result<(), Error> {
        // Each write operation is submitted directly to virtio block, so we don't need to do anything here.
        Ok(())
    }

    fn fsync(&self) -> Result<(), Error> {
        if self.type_() != InodeFileType::Regular {
            error!("[FatInode] fsync: not a file");
            return Err(code::ENOTSUP);
        }
        let mut inner = self.inner.write();
        let (file, _) = inner.as_file_mut().unwrap().internal_file.get_mut();
        file.flush()?;
        Ok(())
    }

    fn file_attr(&self) -> FileAttr {
        match self.fs() {
            Some(fs) => {
                let inner = self.inner.read();
                let dev = fs.fs_info().dev;
                FileAttr::new(dev, 0, &inner.attr)
            }
            None => FileAttr::default(),
        }
    }

    delegate! {
        to self.inner.read().attr {
            fn ino(&self) -> InodeNo;
            fn type_(&self) -> InodeFileType;
            fn mode(&self) -> InodeMode;
            fn size(&self) -> usize;
            fn atime(&self) -> Duration;
            fn mtime(&self) -> Duration;
        }
        to self.inner.write().attr {
            fn set_atime(&self, time: Duration);
            fn set_mtime(&self, time: Duration);
        }
    }
}

impl Drop for FatInode {
    fn drop(&mut self) {
        trace!("Drop {:?}", self)
    }
}

impl core::fmt::Debug for FatInode {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FatInode [{:p}]", self)
    }
}

struct InternalFsWrapper {
    fs: &'static fatfs::FileSystem<FatStorage>,
    lock: Arc<Mutex<()>>,
}

impl Drop for InternalFsWrapper {
    fn drop(&mut self) {
        trace!("[FatFileSystem] drop internal fs wrapper");
        let fs =
            unsafe { Box::from_raw(self.fs as *const _ as *mut fatfs::FileSystem<FatStorage>) };
        drop(fs);
    }
}

impl InternalFsWrapper {
    fn get(&self) -> (&'static fatfs::FileSystem<FatStorage>, MutexGuard<'_, ()>) {
        (self.fs, self.lock.lock())
    }

    fn wrap<T>(&self, content: T) -> InternalFsLock<T> {
        InternalFsLock {
            content,
            lock: self.lock.clone(),
        }
    }
}

static INTERNAL_FS_INSTANCES: RwLock<BTreeMap<String, &'static InternalFsWrapper>> =
    RwLock::new(BTreeMap::new());

fn get_internal_fs_with_guard(
    name: &String,
) -> (&'static fatfs::FileSystem<FatStorage>, MutexGuard<'_, ()>) {
    let internal_fs_wrapper: &'static InternalFsWrapper =
        INTERNAL_FS_INSTANCES.read().get(name).unwrap();
    internal_fs_wrapper.get()
}

struct InternalFsLock<T> {
    content: T,
    lock: Arc<Mutex<()>>,
}

impl<T> InternalFsLock<T> {
    fn get(&self) -> (&T, MutexGuard<'_, ()>) {
        (&self.content, self.lock.lock())
    }

    fn get_mut(&mut self) -> (&mut T, MutexGuard<'_, ()>) {
        (&mut self.content, self.lock.lock())
    }
}

#[derive(Clone)]
pub(crate) struct FatStorage {
    device: Arc<dyn Device>,
    position: u64,              // index of bytes
    pub(crate) total_size: u64, // total size in bytes
    pub(crate) sector_size: u16,
    pub(crate) sector_num: u64,
}

impl IoBase for FatStorage {
    type Error = FatStorageError;
}

impl FatStorage {
    pub(crate) fn new(device_name: &str) -> Result<Self, Error> {
        let block_device = DeviceManager::get()
            .get_block_device(device_name)
            .ok_or(code::ENODEV)?;
        let sector_size = block_device.sector_size().unwrap();
        let sector_num = block_device.capacity().unwrap();
        let total_size = sector_num * (sector_size as u64);
        let storage = Self {
            device: block_device,
            position: 0,
            total_size,
            sector_size,
            sector_num,
        };
        Ok(storage)
    }
}

impl Read for FatStorage {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let read_size = match self.device.read(self.position, buf, false) {
            Ok(read_size) => read_size,
            Err(error) => {
                return Err(error.into());
            }
        };
        self.position += read_size as u64;
        Ok(read_size)
    }
}

impl Write for FatStorage {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let write_size = match self.device.write(self.position, buf, false) {
            Ok(write_size) => write_size,
            Err(error) => {
                return Err(error.into());
            }
        };
        self.position += write_size as u64;
        Ok(write_size)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        if let Err(error) = self.device.sync() {
            return Err(error.into());
        };
        Ok(())
    }
}

impl Seek for FatStorage {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let new_pos = match pos {
            SeekFrom::Start(offset) => offset,
            SeekFrom::End(offset) => {
                let end = self.total_size;
                end.saturating_add(offset as u64)
            }
            SeekFrom::Current(offset) => {
                if offset >= 0 {
                    self.position.saturating_add(offset.unsigned_abs())
                } else {
                    self.position.saturating_sub(offset.unsigned_abs())
                }
            }
        };
        if new_pos > self.total_size {
            return Err(ErrorKind::InvalidInput.into());
        }
        self.position = new_pos;
        Ok(self.position)
    }
}

impl Drop for FatStorage {
    fn drop(&mut self) {
        trace!("[FatStorage] drop");
        let _ = self.device.sync();
    }
}

impl core::fmt::Display for FatStorage {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "FatStorage[sector_size: {}, sector_num {}, total_size: {}] ",
            self.sector_size, self.sector_num, self.total_size
        ))
    }
}

// Add several required error types based on ErrorKind
#[derive(Debug)]
pub enum FatStorageError {
    BasicError(ErrorKind),
    UnexpectedEof,
}

impl fatfs::IoError for FatStorageError {
    fn is_interrupted(&self) -> bool {
        match self {
            FatStorageError::BasicError(e) => *e == ErrorKind::Interrupted,
            _ => false,
        }
    }

    fn new_unexpected_eof_error() -> Self {
        Self::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        Self::BasicError(ErrorKind::WriteZero)
    }
}

impl From<ErrorKind> for FatStorageError {
    fn from(value: ErrorKind) -> Self {
        FatStorageError::BasicError(value)
    }
}
