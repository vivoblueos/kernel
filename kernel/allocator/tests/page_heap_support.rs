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

use allocator_crate::page_heap::{Area, PageHeap, PageSpan, PageWindow, PAGE_SIZE};
use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    ptr::NonNull,
};

#[must_use]
struct TestMemory {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl TestMemory {
    fn new(layout: Layout) -> Self {
        let ptr = NonNull::new(unsafe { alloc_zeroed(layout) }).unwrap();
        Self { ptr, layout }
    }
}

impl Drop for TestMemory {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr.as_ptr(), self.layout) };
    }
}

#[must_use]
pub struct Fixture {
    pub heap: PageHeap,
    pub window: PageWindow,
    free: Vec<bool>,
    // Keep the owned storage alive until after the heap's metadata borrow ends.
    #[allow(dead_code)]
    metadata: Vec<TestMemory>,
    #[allow(dead_code)]
    arena: TestMemory,
}

impl Fixture {
    pub fn new(pages: usize) -> Self {
        let arena = TestMemory::new(Layout::from_size_align(pages * PAGE_SIZE, 65536).unwrap());
        let metadata = Vec::new();
        let window = unsafe { PageWindow::new(arena.ptr, pages) }.unwrap();
        let heap = unsafe { PageHeap::new(window) }.unwrap();
        Self {
            heap,
            window,
            free: vec![true; pages],
            metadata,
            arena,
        }
    }

    pub fn free_pages(&self) -> usize {
        self.free.iter().filter(|free| **free).count()
    }

    pub fn take(&mut self, pages: usize, align: usize) -> Option<PageSpan> {
        if pages == 0 || !align.is_power_of_two() || pages > self.free_pages() {
            return None;
        }
        let first = (0..=self.free.len() - pages).find(|first| {
            let address = self.window.base().as_ptr().addr() + first * PAGE_SIZE;
            address & (align - 1) == 0 && self.free[*first..*first + pages].iter().all(|f| *f)
        })?;
        self.free[first..first + pages].fill(false);
        let span = self.window.span(first, pages).unwrap();
        let metadata = TestMemory::new(Layout::new::<Area>());
        let node = metadata.ptr.cast::<Area>();
        unsafe {
            node.as_ptr()
                .write(Area::new(span.start().as_ptr().addr(), pages).unwrap());
        }
        self.metadata.push(metadata);
        Some(unsafe { span.with_area(node) }.unwrap())
    }

    pub fn release(&mut self, span: PageSpan) {
        let first = self.window.index_of(span.start()).unwrap();
        assert!(self.free[first..first + span.pages()]
            .iter()
            .all(|free| !*free));
        self.free[first..first + span.pages()].fill(true);
    }
}
