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
    vfs::{inode_mode::InodeMode, path},
};
use alloc::sync::Arc;
use log::debug;

pub fn init() -> Result<(), Error> {
    DeviceManager::get().foreach(add_device)
}

fn add_device(path: &str, dev: Arc<dyn Device>) -> Result<(), Error> {
    let mut dev_dir = path::lookup_path("/dev").ok_or(code::ENOENT)?;

    let mut rel_path = path.trim_start_matches('/');
    while !rel_path.is_empty() {
        match rel_path.split_once('/') {
            Some((next_name, next_path)) => {
                rel_path = next_path.trim_start_matches('/');
                dev_dir = dev_dir.lookup(next_name)?;
            }
            None => match dev_dir.lookup(rel_path) {
                Ok(_) => {
                    return Err(code::EEXIST);
                }
                Err(_) => {
                    dev_dir.create_device(
                        rel_path,
                        InodeMode::from_bits_truncate(0o666),
                        dev.clone(),
                    )?;
                    break;
                }
            },
        }
    }

    debug!("[devfs] Added device: {}", path);
    Ok(())
}
