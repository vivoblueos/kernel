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

extern crate alloc;
use core::alloc::Layout;

#[derive(Debug)]
pub enum Storage {
    Alloc(*mut u8, Layout),
    Raw(*mut u8, usize),
}

impl Default for Storage {
    fn default() -> Self {
        Self::Raw(core::ptr::null_mut(), 0)
    }
}

impl Storage {
    #[inline]
    pub fn from_layout(layout: Layout) -> Self {
        let base = unsafe { alloc::alloc::alloc(layout) };
        Storage::Alloc(base, layout)
    }

    #[inline]
    pub fn from_raw(base: *mut u8, size: usize) -> Self {
        Storage::Raw(base, size)
    }

    #[inline]
    pub const fn new() -> Self {
        Storage::Raw(core::ptr::null_mut(), 0)
    }

    #[inline]
    pub fn base(&self) -> *mut u8 {
        match self {
            Storage::Alloc(base, _) => *base,
            Storage::Raw(base, _) => *base,
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        match self {
            Storage::Alloc(_, layout) => layout.size(),
            Storage::Raw(_, size) => *size,
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.base(), self.size()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.base(), self.size()) }
    }
}

impl Drop for Storage {
    #[inline]
    fn drop(&mut self) {
        if let Storage::Alloc(base, layout) = self {
            unsafe { alloc::alloc::dealloc(*base, *layout) }
        }
    }
}
