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

use crate::vfs::{dcache::Dcache, fs::FileSystem, mount::get_mount_manager, tmpfs::TmpFileSystem};
use alloc::{string::String, sync::Arc};
use spin::Once;

static ROOT_DIR: Once<Arc<Dcache>> = Once::new();
pub fn init() {
    ROOT_DIR.call_once(|| -> Arc<Dcache> {
        let rootfs = TmpFileSystem::new();
        let root = Dcache::new_root(rootfs.root_inode());
        get_mount_manager()
            .add_mount(&String::from("/"), root.clone(), rootfs.clone())
            .unwrap();
        root
    });
}

pub fn get_root_dir() -> &'static Arc<Dcache> {
    ROOT_DIR.get().unwrap()
}
