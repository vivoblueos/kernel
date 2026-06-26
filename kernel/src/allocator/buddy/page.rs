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

use crate::types::{impl_simple_intrusive_adapter, IlistHead};
use core::sync::atomic::AtomicUsize;

pub const PAGE_SIZE: usize = 4096;
pub const PAGE_SHIFT: usize = 12;
pub const MAX_ORDER: usize = 11;

/// Page descriptor flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageFlags(pub u8);

impl PageFlags {
    pub const FREE: u8 = 1 << 0;
    pub const RESERVED: u8 = 1 << 1;
    pub const SLAB: u8 = 1 << 2;
    pub const MAPPED: u8 = 1 << 3;

    pub const fn new() -> Self {
        PageFlags(0)
    }

    pub fn contains(self, flag: u8) -> bool {
        (self.0 & flag) != 0
    }

    pub fn set(&mut self, flag: u8) {
        self.0 |= flag;
    }

    pub fn clear(&mut self, flag: u8) {
        self.0 &= !flag;
    }
}

/// Adapter linking [`Page`] into a free-list [`crate::types::Ilist`] via the
/// `list_node` field. Used by [`BuddyAllocatorCore`](super::heap::BuddyAllocatorCore).
impl_simple_intrusive_adapter!(PageListNodeAdapter, Page, list_node);

/// Physical page descriptor.
///
/// Each physical page has one `Page` descriptor. Descriptors are stored
/// in a contiguous array starting from the beginning of physical memory.
#[repr(C)]
pub struct Page {
    /// Intrusive free-list node. Detached (default) when not linked into a
    /// free list; the buddy allocator links it via the typed intrusive list.
    pub list_node: IlistHead<Page, PageListNodeAdapter>,
    pub pfn: usize,
    pub order: u8,
    pub flags: PageFlags,
    pub refcount: AtomicUsize,
}

impl Page {
    pub const fn new() -> Self {
        Page {
            list_node: IlistHead::new(),
            pfn: 0,
            order: 0,
            flags: PageFlags::new(),
            refcount: AtomicUsize::new(0),
        }
    }
}
