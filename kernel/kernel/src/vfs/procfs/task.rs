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

use super::ProcFileOps;
use crate::{
    error::Error,
    thread::{Thread, ThreadNode},
};
use alloc::{format, string::String, vec::Vec};
use core::fmt::Write;

pub struct ProcTaskFile {
    thread: ThreadNode,
}

impl ProcTaskFile {
    pub fn new(thread: ThreadNode) -> Self {
        Self { thread }
    }
}

impl ProcFileOps for ProcTaskFile {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        let mut result = String::with_capacity(64);
        writeln!(result, "{:<9} {}", "Name:", self.thread.kind_to_str()).unwrap();
        writeln!(result, "{:<9} {}", "State:", self.thread.state_to_str()).unwrap();
        writeln!(result, "{:<9} {}", "Tid:", Thread::id(&self.thread)).unwrap();
        writeln!(result, "{:<9} {}", "Priority:", self.thread.priority()).unwrap();
        Ok(result.as_bytes().to_vec())
    }

    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error> {
        Ok(0)
    }
}
