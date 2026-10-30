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

use crate::{allocator, error::Error, vfs::procfs::ProcFileOps};
use alloc::{format, string::String, vec::Vec};
use core::fmt::Write;

pub(crate) struct MemoryInfo;

impl ProcFileOps for MemoryInfo {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        let meminfo = allocator::memory_info();
        let available = meminfo.total - meminfo.used;
        // Pre-allocate buffer with estimated size
        let mut result = String::with_capacity(128);
        writeln!(result, "{:<14}{:>8} kB", "MemTotal:", meminfo.total / 1024).unwrap();
        writeln!(result, "{:<14}{:>8} kB", "MemAvailable:", available / 1024).unwrap();
        writeln!(result, "{:<14}{:>8} kB", "MemUsed:", meminfo.used / 1024).unwrap();
        writeln!(
            result,
            "{:<14}{:>8} kB",
            "MemMaxUsed:",
            meminfo.max_used / 1024
        )
        .unwrap();
        Ok(result.as_bytes().to_vec())
    }

    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error> {
        Ok(0)
    }
}
