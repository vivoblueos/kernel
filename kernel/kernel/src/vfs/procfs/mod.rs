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

mod memory_info;
mod stat;
mod task;

use memory_info::MemoryInfo;
use stat::SystemStat;
use task::ProcTaskFile;

use crate::{
    devices::Device,
    error::{code, Error},
    thread::{GlobalQueueVisitor, Thread, ThreadNode},
    vfs::{
        dirent::DirBufferReader,
        file::FileAttr,
        fs::{FileSystem, FileSystemInfo},
        inode::{InodeAttr, InodeNo, InodeOps},
        inode_mode::{InodeFileType, InodeMode},
        utils::NAME_MAX,
        Dcache,
    },
};
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::{Arc, Weak},
    vec::Vec,
};
use core::{
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    time::Duration,
};
use delegate::delegate;
use log::warn;
use spin::{Once, RwLock};

pub trait ProcFileOps: Send + Sync {
    // Obtain the file content when a read operation is performed on a proc inode.
    fn get_content(&self) -> Result<Vec<u8>, Error>;
    // Set the file content when a write operation is performed on a proc inode.
    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error>;
}

struct DefaultProcFileOps;

impl ProcFileOps for DefaultProcFileOps {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        Ok(Vec::new())
    }

    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error> {
        Ok(0)
    }
}

// same as linux
const MAGIC: usize = 0x9FA0;
const BLOCK_SIZE: usize = 1024;
const ROOT_INO: InodeNo = 1;

static PROCFS: Once<Arc<ProcFileSystem>> = Once::new();

pub fn get_procfs() -> &'static Arc<ProcFileSystem> {
    PROCFS.call_once(ProcFileSystem::new)
}

/// Proc filesystem implementation
#[cfg_attr(feature = "cbindgen", no_mangle)]
pub struct ProcFileSystem {
    root: Arc<ProcDir>,
    // Next available inode number
    next_inode_no: AtomicUsize,
    fs_info: FileSystemInfo,
    is_mounted: AtomicBool,
}

impl ProcFileSystem {
    pub fn new() -> Arc<Self> {
        Arc::new_cyclic(|weak_fs| Self {
            root: Arc::new_cyclic(|weak_root| ProcDir {
                base: BaseNode {
                    attr: RwLock::new(InodeAttr::new(
                        ROOT_INO,
                        InodeFileType::Directory,
                        InodeMode::from_bits_truncate(0o755),
                        0,
                        0,
                        BLOCK_SIZE,
                    )),
                    fs: weak_fs.clone(),
                    is_dcacheable: true,
                },
                this: weak_root.clone(),
                parent: weak_root.clone(),
                children: RwLock::new(BTreeMap::new()),
            }),
            next_inode_no: AtomicUsize::new(ROOT_INO + 1),
            is_mounted: AtomicBool::new(false),
            fs_info: FileSystemInfo::new(MAGIC, 0, NAME_MAX, BLOCK_SIZE, 0),
        })
    }

    /// Allocate new inode number
    fn alloc_inode_no(&self) -> InodeNo {
        self.next_inode_no.fetch_add(1, Ordering::Relaxed)
    }

    fn check_mounted(&self) -> bool {
        self.is_mounted.load(Ordering::Relaxed)
    }

    pub fn is_mounted(&self) -> bool {
        self.is_mounted.load(Ordering::Relaxed)
    }

    pub fn init(&self) -> Result<(), Error> {
        if self.check_mounted() {
            warn!("proc can not be mounted twice");
            return Err(code::EBUSY);
        }
        self.is_mounted.store(true, Ordering::Relaxed);

        self.root.create_meminfo_file("meminfo")?;
        self.root.create_stat_file("stat")?;

        // not support process yet, use thread info instead. and put all threads in /proc
        let mut global_queue_visitor = GlobalQueueVisitor::new();
        while let Some(thread) = global_queue_visitor.next() {
            let id = Thread::id(&thread);
            let id_str = id.to_string();
            log::debug!("create_task_dir: /proc/{}", id_str);
            let thread_dir = self.root.create_dir(id_str.as_str(), false)?;
            let _ = thread_dir.create_task_file("status", thread.clone())?;
        }

        Ok(())
    }
}

impl FileSystem for ProcFileSystem {
    fn mount(&self, _mount_point: Arc<Dcache>) -> Result<(), Error> {
        if self.check_mounted() {
            warn!("Filesystem already mounted!");
            return Err(code::EBUSY);
        }

        self.init()?;
        Ok(())
    }
    fn unmount(&self) -> Result<(), Error> {
        if !self.check_mounted() {
            return Err(code::EINVAL);
        }
        self.is_mounted.store(false, Ordering::Relaxed);
        Ok(())
    }
    fn sync(&self) -> Result<(), Error> {
        // do nothing
        Ok(())
    }
    fn root_inode(&self) -> Arc<dyn InodeOps> {
        self.root.clone()
    }
    fn fs_info(&self) -> FileSystemInfo {
        self.fs_info.clone()
    }
    fn fs_type(&self) -> &str {
        "procfs"
    }
}

#[derive(Debug)]
struct BaseNode {
    attr: RwLock<InodeAttr>,
    fs: Weak<ProcFileSystem>,
    is_dcacheable: bool,
}

impl BaseNode {
    pub fn inode_attr(&self) -> InodeAttr {
        self.attr.read().clone()
    }

    pub fn file_attr(&self) -> FileAttr {
        FileAttr::new(0, 0, &self.inode_attr())
    }

    pub fn is_dcacheable(&self) -> bool {
        self.is_dcacheable
    }

    pub fn fs(&self) -> Option<Arc<dyn FileSystem>> {
        match self.fs.upgrade() {
            Some(fs) => Some(fs),
            None => None,
        }
    }

    delegate! {
        to self.attr.read() {
            fn ino(&self) -> InodeNo;
            fn type_(&self) -> InodeFileType;
            fn size(&self) -> usize;
            fn mode(&self) -> InodeMode;
            fn atime(&self) -> Duration;
            fn mtime(&self) -> Duration;
        }
        to self.attr.write() {
            fn set_atime(&self, time: Duration);
            fn set_mtime(&self, time: Duration);
        }
    }
}

#[derive(Debug)]
struct ProcDir {
    base: BaseNode,
    this: Weak<ProcDir>,
    parent: Weak<ProcDir>,
    children: RwLock<BTreeMap<String, Arc<dyn InodeOps>>>,
}

impl ProcDir {
    pub fn create_task_file(
        &self,
        name: &str,
        thread: ThreadNode,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }

        let ino = self.base.fs.upgrade().unwrap().alloc_inode_no();
        let inode = ProcFile::new(ProcTaskFile::new(thread), ino, self.base.fs.clone(), false)
            as Arc<dyn InodeOps>;
        self.insert(name, inode.clone());

        Ok(inode)
    }

    pub fn create_meminfo_file(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }
        let ino = self.base.fs.upgrade().unwrap().alloc_inode_no();
        let inode =
            ProcFile::new(MemoryInfo {}, ino, self.base.fs.clone(), true) as Arc<dyn InodeOps>;
        self.insert(name, inode.clone());
        Ok(inode)
    }

    pub fn create_stat_file(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }
        let ino = self.base.fs.upgrade().unwrap().alloc_inode_no();
        let inode =
            ProcFile::new(SystemStat {}, ino, self.base.fs.clone(), true) as Arc<dyn InodeOps>;
        self.insert(name, inode.clone());
        Ok(inode)
    }

    pub fn create_dir(&self, name: &str, is_dcacheable: bool) -> Result<Arc<Self>, Error> {
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }
        let ino = self.base.fs.upgrade().unwrap().alloc_inode_no();
        let inode = Arc::new_cyclic(|weak_inode| ProcDir {
            base: BaseNode {
                attr: RwLock::new(InodeAttr::new(
                    ino,
                    InodeFileType::Directory,
                    InodeMode::from(0o555),
                    0,
                    0,
                    BLOCK_SIZE,
                )),
                fs: self.base.fs.clone(),
                is_dcacheable,
            },
            this: weak_inode.clone(),
            parent: self.this.clone(),
            children: RwLock::new(BTreeMap::new()),
        });
        self.insert(name, inode.clone());

        Ok(inode)
    }

    fn find(&self, name: &str) -> Option<Arc<dyn InodeOps>> {
        self.children.read().get(name).cloned()
    }

    fn insert(&self, name: &str, inode: Arc<dyn InodeOps>) {
        self.children.write().insert(String::from(name), inode);
    }

    fn remove(&self, name: &str) {
        self.children.write().remove(name);
    }
}

impl InodeOps for ProcDir {
    fn lookup(&self, name: &str) -> Result<Arc<dyn InodeOps>, Error> {
        // some proc is not cacheable, so we don't need to deal with the "." and ".."
        if name == "." {
            return Ok(self.this.upgrade().unwrap());
        }
        if name == ".." {
            return Ok(self.parent.upgrade().unwrap());
        }
        let inode = self.find(name).ok_or(code::ENOENT)?;
        Ok(inode.clone())
    }

    fn getdents_at(&self, offset: usize, reader: &mut DirBufferReader) -> Result<usize, Error> {
        let mut count = 0;
        let mut current_offset = offset;
        // Handle special entries (., ..)
        if current_offset == 0 {
            match reader.write_node(self.ino(), current_offset as i64, self.type_(), ".") {
                Ok(_) => {
                    count += 1;
                    current_offset += 1;
                }
                Err(e) => return Err(e),
            }
        }

        if current_offset == 1 {
            if let Err(e) = reader.write_node(self.ino(), current_offset as i64, self.type_(), "..")
            {
                if count == 0 {
                    return Err(e);
                }
                return Ok(count);
            }
            count += 1;
            current_offset += 1;
        }

        let start_idx = current_offset.saturating_sub(2);
        for (name, inode) in self.children.read().iter().skip(start_idx) {
            match reader.write_node(inode.ino(), current_offset as i64, inode.type_(), name) {
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

    fn create(
        &self,
        _name: &str,
        _type_: InodeFileType,
        _mode: InodeMode,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        Err(code::EPERM)
    }

    fn create_device(
        &self,
        _name: &str,
        _mode: InodeMode,
        _device: Arc<dyn Device>,
    ) -> Result<Arc<dyn InodeOps>, Error> {
        Err(code::EPERM)
    }

    fn link(&self, _old: &Arc<dyn InodeOps>, _name: &str) -> Result<(), Error> {
        Err(code::EPERM)
    }

    fn unlink(&self, _name: &str) -> Result<(), Error> {
        Err(code::EPERM)
    }

    fn rmdir(&self, _name: &str) -> Result<(), Error> {
        Err(code::EPERM)
    }

    delegate! {
        to self.base {
            fn inode_attr(&self) -> InodeAttr;
            fn file_attr(&self) -> FileAttr;
            fn is_dcacheable(&self) -> bool;
            fn ino(&self) -> InodeNo;
            fn type_(&self) -> InodeFileType;
            fn size(&self) -> usize;
            fn mode(&self) -> InodeMode;
            fn atime(&self) -> Duration;
            fn set_atime(&self, time: Duration);
            fn mtime(&self) -> Duration;
            fn set_mtime(&self, time: Duration);
            fn fs(&self) -> Option<Arc<dyn FileSystem>>;
        }
    }
}

struct ProcFile<T: ProcFileOps> {
    base: BaseNode,
    inner: T,
    snapshot: RwLock<Vec<u8>>,
}

impl<T: ProcFileOps> ProcFile<T> {
    pub fn new(
        file: T,
        inode_no: InodeNo,
        fs: Weak<ProcFileSystem>,
        is_dcacheable: bool,
    ) -> Arc<Self> {
        Arc::new(Self {
            base: BaseNode {
                attr: RwLock::new(InodeAttr::new(
                    inode_no,
                    InodeFileType::Regular,
                    InodeMode::from(0o444),
                    0,
                    0,
                    BLOCK_SIZE,
                )),
                fs: fs.clone(),
                is_dcacheable,
            },
            inner: file,
            snapshot: RwLock::new(Vec::new()),
        })
    }
}

impl<T: ProcFileOps + 'static> InodeOps for ProcFile<T> {
    fn read_at(&self, offset: usize, buf: &mut [u8], _nonblock: bool) -> Result<usize, Error> {
        if offset == 0 {
            let content = self.inner.get_content()?;
            let mut w = self.snapshot.write();
            w.clear();
            w.extend_from_slice(&content);
            drop(w);
        }

        let snapshot = self.snapshot.read();
        let start = snapshot.len().min(offset);
        let end = snapshot.len().min(offset + buf.len());
        let len = end - start;
        buf[0..len].copy_from_slice(&snapshot[start..end]);

        Ok(len)
    }

    fn write_at(&self, _offset: usize, _buf: &[u8], _nonblock: bool) -> Result<usize, Error> {
        Err(code::EPERM)
    }

    fn resize(&self, _new_size: usize) -> Result<(), Error> {
        Err(code::EPERM)
    }

    delegate! {
        to self.base {
            fn inode_attr(&self) -> InodeAttr;
            fn file_attr(&self) -> FileAttr;
            fn is_dcacheable(&self) -> bool;
            fn ino(&self) -> InodeNo;
            fn type_(&self) -> InodeFileType;
            fn size(&self) -> usize;
            fn mode(&self) -> InodeMode;
            fn atime(&self) -> Duration;
            fn set_atime(&self, time: Duration);
            fn mtime(&self) -> Duration;
            fn set_mtime(&self, time: Duration);
            fn fs(&self) -> Option<Arc<dyn FileSystem>>;
        }
    }
}

// TODO: add observer to trace create and close when process is supported.
pub fn trace_thread_create(thread: ThreadNode) -> Result<(), Error> {
    let procfs = get_procfs();
    if !procfs.is_mounted() {
        return Err(code::EINVAL);
    }
    let root = procfs.root.clone();
    let pid_dir = root.lookup("0")?;
    let task_dir = pid_dir.lookup("task")?;
    let task_dir = task_dir.downcast_ref::<ProcDir>().ok_or(code::EINVAL)?;
    let thread_dir = task_dir.create_dir(Thread::id(&thread).to_string().as_str(), false)?;
    let _ = thread_dir.create_task_file("status", thread.clone())?;
    Ok(())
}

pub fn trace_thread_close(thread: ThreadNode) -> Result<(), Error> {
    let procfs = get_procfs();
    if !procfs.is_mounted() {
        return Err(code::EINVAL);
    }
    let root = procfs.root.clone();
    let pid_dir = root.lookup("0")?;
    let task_dir = pid_dir.lookup("task")?;
    let task_dir = task_dir.downcast_ref::<ProcDir>().ok_or(code::EINVAL)?;
    task_dir.remove(Thread::id(&thread).to_string().as_str());
    Ok(())
}
