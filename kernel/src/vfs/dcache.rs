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
        fs::{FileSystem, FileSystemInfo},
        inode::InodeOps,
        inode_mode::{InodeFileType, InodeMode},
        mount::get_mount_manager,
        utils::NAME_MAX,
    },
};
use alloc::{
    collections::BTreeMap,
    format,
    string::String,
    sync::{Arc, Weak},
};
use core::{
    fmt::{self, Debug},
    ptr,
    sync::atomic::{AtomicBool, Ordering},
    time::Duration,
};
use delegate::delegate;
use log::{debug, error, trace};
use spin::RwLock;

/// File system lookup cache
pub struct Dcache {
    // inode will never change after creation
    inode: Arc<dyn InodeOps>,
    // name and parent may change by rename, None means root directory
    name_and_parent: RwLock<Option<(String, Weak<Dcache>)>>,
    children: RwLock<BTreeMap<String, Arc<Dcache>>>,
    // When a child path becomes a mount point of other fs, it will be cached here
    overridden_children: RwLock<Option<BTreeMap<String, Arc<Dcache>>>>,
    // use to set parent in children
    this: Weak<Dcache>,
    is_mount_point: AtomicBool,
}

impl Dcache {
    /// Create new directory node
    pub fn new(inode: Arc<dyn InodeOps>, name: String, parent: Weak<Dcache>) -> Arc<Self> {
        Arc::new_cyclic(|weak_self| Self {
            inode,
            name_and_parent: RwLock::new(Some((name, parent))),
            children: RwLock::new(BTreeMap::new()),
            this: weak_self.clone(),
            is_mount_point: AtomicBool::new(false),
            overridden_children: RwLock::new(None),
        })
    }

    pub fn new_root(inode: Arc<dyn InodeOps>) -> Arc<Self> {
        Arc::new_cyclic(|weak_self| Self {
            inode,
            name_and_parent: RwLock::new(None),
            children: RwLock::new(BTreeMap::new()),
            this: weak_self.clone(),
            is_mount_point: AtomicBool::new(false),
            overridden_children: RwLock::new(None),
        })
    }

    pub fn new_child<F>(
        &self,
        name: &str,
        type_: InodeFileType,
        mode: InodeMode,
        inode_creator: F,
    ) -> Result<Arc<Self>, Error>
    where
        F: FnOnce() -> Option<Arc<dyn InodeOps>>,
    {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        if name == "." || name == ".." {
            return Err(code::EEXIST);
        }
        let mut children = self.children.write();
        if children.contains_key(name) {
            return Err(code::EEXIST);
        }
        let inode =
            inode_creator().unwrap_or_else(|| self.inode.create(name, type_, mode).unwrap());
        let child = Self::new(inode, String::from(name), self.get_weak_ref());
        if child.is_dcacheable() {
            children.insert(String::from(name), child.clone());
        }
        Ok(child)
    }

    pub fn create_device(
        &self,
        name: &str,
        mode: InodeMode,
        dev: Arc<dyn Device>,
    ) -> Result<Arc<Self>, Error> {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let mut children = self.children.write();
        if children.contains_key(name) {
            return Err(code::EEXIST);
        }

        let inode = self.inode.create_device(name, mode, dev)?;
        let name_str = String::from(name);
        let child = Self::new(inode, name_str.clone(), self.get_weak_ref());
        if child.is_dcacheable() {
            children.insert(name_str, child.clone());
        }
        Ok(child)
    }

    pub fn lookup(&self, name: &str) -> Result<Arc<Dcache>, Error> {
        if name.len() > NAME_MAX {
            return Err(code::ENAMETOOLONG);
        }

        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }

        if !self.inode.mode().contains(InodeMode::S_IXUSR) {
            return Err(code::ENOTDIR);
        }

        let this = self.this.upgrade().unwrap();
        let entry = match name {
            "." => this,
            ".." => self.parent().unwrap_or(this),
            name => {
                // find in dcache first
                match self.find_child(name) {
                    Some(child) => child,
                    None => {
                        // lookup in filesystem
                        let inode = self.inode.lookup(name)?;
                        let entry = Dcache::new(inode, String::from(name), self.get_weak_ref());
                        self.add_child(String::from(name), &entry);
                        entry
                    }
                }
            }
        };

        Ok(entry)
    }

    /// Add child node
    pub fn add_child(&self, name: String, child: &Arc<Dcache>) {
        self.children.write().insert(name, child.clone());
    }

    /// Remove child node
    pub fn remove_child(&self, name: &str) -> Option<Arc<Dcache>> {
        self.children.write().remove(name)
    }

    /// Find child node
    pub fn find_child(&self, name: &str) -> Option<Arc<Dcache>> {
        let children = self.children.read();
        children.get(name).cloned()
    }

    fn set_name_and_parent(&self, name: &str, parent: Weak<Self>) {
        let mut name_and_parent = self.name_and_parent.write();
        *name_and_parent = Some((String::from(name), parent));
    }

    pub fn name(&self) -> String {
        match self.name_and_parent.read().as_ref() {
            Some(x) => x.0.clone(),
            None => String::from("/"),
        }
    }

    pub fn parent(&self) -> Option<Arc<Dcache>> {
        match self.name_and_parent.read().as_ref() {
            Some((_, parent)) => parent.upgrade(),
            None => None,
        }
    }

    pub fn inode(&self) -> &Arc<dyn InodeOps> {
        &self.inode
    }

    pub fn fs_info(&self) -> FileSystemInfo {
        match self.inode.fs() {
            Some(fs) => fs.fs_info(),
            None => FileSystemInfo::default(),
        }
    }

    pub fn is_mount_point(&self) -> bool {
        self.is_mount_point.load(Ordering::Acquire)
    }

    /// Get full path
    pub fn get_full_path(&self) -> String {
        // Handle root directory case
        if self.name_and_parent.read().as_ref().is_none() {
            return String::from("/");
        }

        let mut path = self.name();
        let mut current = self.parent();

        while let Some(node) = current {
            let parent_name = node.name();
            if parent_name != "/" {
                path = format!("{}/{}", parent_name, path);
            }
            current = node.parent();
        }
        path = format!("/{}", path);
        path
    }

    pub fn mount(&self, fs: Arc<dyn FileSystem>) -> Result<(), Error> {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }

        if self.is_mount_point() {
            error!("Directory is already a mount point");
            return Err(code::EBUSY);
        }

        fs.mount(self.this.upgrade().unwrap())?;
        let name_and_parent = self.name_and_parent.read();
        if let Some((name, parent)) = name_and_parent.as_ref() {
            if let Some(parent) = parent.upgrade() {
                parent.add_mount_point(self.name(), self.this.upgrade().unwrap())?;
            }
        } else {
            error!("The root directory is not allowed to mount");
            return Err(code::ENOTSUP);
        }

        self.is_mount_point.store(true, Ordering::Release);

        let mount_manager = get_mount_manager();
        mount_manager.add_mount(&self.get_full_path(), self.this.upgrade().unwrap(), fs)
    }

    pub fn unmount(&self) -> Result<(), Error> {
        if !self.is_mount_point() {
            error!("Directory is not a mount point");
            return Err(code::EINVAL);
        }

        self.inode.fs().unwrap().unmount()?;

        let name_and_parent = self.name_and_parent.read();
        if let Some((name, parent)) = name_and_parent.as_ref() {
            if let Some(parent) = parent.upgrade() {
                parent.remove_mount_point(self.name())?;
            }
        } else {
            error!("The root directory is not allowed to unmount");
            return Err(code::ENOTSUP);
        }

        self.is_mount_point.store(false, Ordering::Release);

        let mount_manager = get_mount_manager();
        mount_manager.remove_mount(&self.get_full_path())
    }

    pub fn link(&self, old: &Arc<Dcache>, new_name: &str) -> Result<(), Error> {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let mut children = self.children.write();
        if children.contains_key(new_name) {
            return Err(code::EEXIST);
        }

        self.inode.link(&old.inode, new_name)?;
        let new_name_str = String::from(new_name);
        let new_child = Self::new(old.inode.clone(), new_name_str.clone(), self.get_weak_ref());
        if new_child.is_dcacheable() {
            children.insert(new_name_str, new_child);
        }
        Ok(())
    }

    /// Unlink a file or directory
    pub fn unlink(&self, name: &str) -> Result<(), Error> {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let mut children = self.children.write();
        let Some(child) = children.get(name) else {
            return Err(code::ENOENT);
        };
        if child.is_mount_point() {
            return Err(code::EBUSY);
        }

        self.inode.unlink(name)?;
        children.remove(name);
        Ok(())
    }

    pub fn rmdir(&self, name: &str) -> Result<(), Error> {
        if self.inode.type_() != InodeFileType::Directory {
            return Err(code::ENOTDIR);
        }
        let mut children = self.children.write();
        let Some(child) = children.get(name) else {
            return Err(code::ENOENT);
        };
        if child.is_mount_point() {
            return Err(code::EBUSY);
        }
        self.inode.rmdir(name)?;
        children.remove(name);
        Ok(())
    }

    pub fn rename(
        &self,
        old_name: &str,
        new_dir: &Arc<Dcache>,
        new_name: &str,
    ) -> Result<(), Error> {
        if self.inode.type_() != InodeFileType::Directory
            || new_dir.inode.type_() != InodeFileType::Directory
        {
            return Err(code::ENOTDIR);
        }

        if old_name == "." || old_name == ".." || new_name == "." || new_name == ".." {
            error!("Invalid name: {} to {}", old_name, new_name);
            return Err(code::EINVAL);
        }

        let mut children = self.children.write();
        let child = match children.get(old_name) {
            Some(child) => child.clone(),
            None => {
                debug!("{} not found", old_name);
                return Err(code::ENOENT);
            }
        };
        if child.is_mount_point() {
            debug!("{} is a mount point", old_name);
            return Err(code::EBUSY);
        }

        // rename in the same directory
        if ptr::addr_eq(self, Arc::as_ptr(new_dir)) && old_name != new_name {
            if children.contains_key(new_name) {
                debug!("{} already exists", new_name);
                return Err(code::EEXIST);
            }
            self.inode.rename(old_name, &self.inode, new_name)?;
            children.remove(old_name);
            if child.is_dcacheable() {
                children.insert(String::from(new_name), child);
            }
        } else {
            let mut new_children = new_dir.children.write();
            if new_children.contains_key(new_name) {
                debug!("{} already exists", new_name);
                return Err(code::EEXIST);
            }
            self.inode.rename(old_name, &new_dir.inode, new_name)?;
            children.remove(old_name);
            child.set_name_and_parent(new_name, new_dir.this.clone());
            if child.is_dcacheable() {
                new_children.insert(String::from(new_name), child);
            }
        }

        Ok(())
    }

    fn add_mount_point(&self, name: String, mount_point: Arc<Dcache>) -> Result<(), Error> {
        trace!("Add mount point: {} , {:?}", name, mount_point);
        let mut overridden_children = self.overridden_children.write();
        if overridden_children.is_none() {
            *overridden_children = Some(BTreeMap::new());
        }
        let mut children = self.children.write();
        if let Some(overridden_child) = children.remove(&name) {
            if let Some(overridden_children) = overridden_children.as_mut() {
                overridden_children.insert(overridden_child.name(), overridden_child);
            }
        }

        children.insert(name, mount_point);
        Ok(())
    }

    fn remove_mount_point(&self, name: String) -> Result<(), Error> {
        let mut children = self.children.write();
        trace!(
            "Remove mount point: {} , {:?}",
            name,
            children.remove(&name).unwrap()
        );

        let mut overridden_children = self.overridden_children.write();
        let overridden_point = overridden_children.as_mut().unwrap().remove(&name);
        if let Some(overridden_point) = overridden_point {
            trace!(
                "Reinsert overridden directory: {} , {:?}",
                name,
                overridden_point
            );
            children.insert(name, overridden_point);
        }

        Ok(())
    }

    /// Get a copy of its own weak reference
    #[inline(always)]
    pub(crate) fn get_weak_ref(&self) -> Weak<Self> {
        self.this.clone()
    }

    delegate! {
        to self.inode {
            pub fn fs(&self) -> Option<Arc<dyn FileSystem>>;
            pub fn fsync(&self) -> Result<(), Error>;
            pub fn size(&self) -> usize;
            pub fn resize(&self, size: usize) -> Result<(), Error>;
            pub fn type_(&self) -> InodeFileType;
            pub fn mode(&self) -> InodeMode;
            pub fn atime(&self) -> Duration;
            pub fn set_atime(&self, time: Duration);
            pub fn mtime(&self) -> Duration;
            pub fn set_mtime(&self, time: Duration);
            pub fn is_dcacheable(&self) -> bool;
        }
    }
}

impl Debug for Dcache {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Dcache {{ inode: {:p}, name: {}, fs {} }}",
            self.inode,
            self.get_full_path(),
            match self.inode.fs() {
                Some(fs) => String::from(fs.fs_type()),
                None => String::from("unknown"),
            },
        )
    }
}

impl Drop for Dcache {
    fn drop(&mut self) {
        trace!("Drop {:?}", self);
    }
}
