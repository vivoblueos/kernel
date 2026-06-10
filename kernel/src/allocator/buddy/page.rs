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

use core::{ptr, sync::atomic::AtomicUsize};

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

/// Intrusive doubly-linked list node embedded within [`Page`].
#[derive(Debug, Clone, Copy)]
pub struct LinkedListNode {
    pub next: *mut Page,
    pub prev: *mut Page,
}

impl LinkedListNode {
    pub const fn new() -> Self {
        LinkedListNode {
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

/// Physical page descriptor.
///
/// Each physical page has one `Page` descriptor. Descriptors are stored
/// in a contiguous array starting from the beginning of physical memory.
#[repr(C)]
pub struct Page {
    pub list: LinkedListNode,
    pub pfn: usize,
    pub order: u8,
    pub flags: PageFlags,
    pub refcount: AtomicUsize,
}

impl Page {
    pub const fn new() -> Self {
        Page {
            list: LinkedListNode::new(),
            pfn: 0,
            order: 0,
            flags: PageFlags::new(),
            refcount: AtomicUsize::new(0),
        }
    }
}

/// Intrusive doubly-linked list of `Page` descriptors.
///
/// Uses the `list` field embedded in each `Page` for linkage.
/// No heap allocations — all nodes are `Page` structs in the mem_map array.
#[derive(Clone, Copy)]
pub struct LinkedList {
    head: *mut Page,
}

impl LinkedList {
    pub const fn new() -> Self {
        LinkedList {
            head: ptr::null_mut(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Insert `page` at the head of the list.
    pub unsafe fn push(&mut self, page: *mut Page) {
        (*page).list.next = self.head;
        (*page).list.prev = ptr::null_mut();
        if !self.head.is_null() {
            (*self.head).list.prev = page;
        }
        self.head = page;
    }

    /// Remove `page` from the list.
    ///
    /// # Safety
    /// `page` must be currently present in this list.
    pub unsafe fn remove(&mut self, page: *mut Page) {
        let prev = (*page).list.prev;
        let next = (*page).list.next;

        if prev.is_null() {
            self.head = next;
        } else {
            (*prev).list.next = next;
        }

        if !next.is_null() {
            (*next).list.prev = prev;
        }

        (*page).list.next = ptr::null_mut();
        (*page).list.prev = ptr::null_mut();
    }

    /// Pop the head page from the list.
    pub unsafe fn pop(&mut self) -> Option<*mut Page> {
        if self.head.is_null() {
            return None;
        }
        let page = self.head;
        self.head = (*page).list.next;
        if !self.head.is_null() {
            (*self.head).list.prev = ptr::null_mut();
        }
        (*page).list.next = ptr::null_mut();
        (*page).list.prev = ptr::null_mut();
        Some(page)
    }

    /// Peek at the head page without removing.
    pub fn peek(&self) -> Option<*mut Page> {
        if self.head.is_null() {
            None
        } else {
            Some(self.head)
        }
    }
}
