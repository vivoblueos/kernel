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

use alloc::boxed::Box;
use blueos::{
    allocator, irq, scheduler,
    scheduler::InsertToEnd,
    support::Storage,
    sync::{Semaphore, SpinLock},
    types::{Arc, Uint},
};
use blueos_infra::{
    impl_simple_intrusive_adapter,
    list::typed_ilist::{ListHead, ListHeadIterator},
};
use core::alloc::Layout;

// FIXME: We haven't got builtin memory pool API in allocator, so we just use
// HEAP's public API to implement the memory pool. There might be performance degradation.

type BlockList = ListHead<Block, Node>;
type BlockListIterator = ListHeadIterator<Block, Node>;

#[derive(Debug)]
struct MemoryPoolInner {
    block_size: usize,
    total_blocks: usize,
    free_blocks: usize,
    free_list: BlockList,
    busy_list: BlockList,
}

impl MemoryPoolInner {
    fn new() -> Self {
        Self {
            block_size: 0,
            total_blocks: 0,
            free_blocks: 0,
            free_list: BlockList::new(),
            busy_list: BlockList::new(),
        }
    }

    #[allow(clippy::type_complexity)]
    fn init(&mut self, block_count: usize, block_size: usize, at: Option<&mut [u8]>) {
        self.block_size = block_size;
        self.total_blocks = block_count;
        const ALIGN: usize = core::mem::align_of::<usize>();
        let mut storage_ctor: Box<dyn Fn(usize, &mut Block)> = if let Some(raw) = at {
            let base = raw.as_mut_ptr();
            Box::new(move |i, block: &mut Block| {
                block.set_storage(Storage::Raw(
                    unsafe { base.add(i * block_size) },
                    block_size,
                ));
            })
        } else {
            Box::new(|i, block: &mut Block| {
                let layout = Layout::from_size_align(block_size, ALIGN).unwrap();
                block.set_storage(Storage::from_layout(layout));
            })
        };
        for i in 0..block_count {
            let mut block = Box::new(Block::new());
            storage_ctor(i, &mut block);
            let ok = BlockList::insert_after(&mut self.free_list, &mut block.node);
            debug_assert!(ok);
            self.free_blocks += 1;
            let _ = Box::into_raw(block);
        }
    }
}

impl_simple_intrusive_adapter!(Node, Block, node);

#[derive(Debug)]
#[repr(C)]
struct Block {
    node: BlockList,
    storage: Storage,
}

impl Block {
    const fn new() -> Self {
        Self {
            node: BlockList::new(),
            storage: Storage::new(),
        }
    }

    fn set_storage(&mut self, storage: Storage) -> &mut Self {
        self.storage = storage;
        self
    }

    #[inline]
    fn base(&self) -> *mut u8 {
        self.storage.base()
    }
}

#[derive(Debug)]
pub struct MemoryPool {
    sema: Semaphore,
    inner: SpinLock<MemoryPoolInner>,
}

impl MemoryPool {
    pub fn new() -> Self {
        Self {
            sema: Semaphore::new(),
            inner: SpinLock::new(MemoryPoolInner::new()),
        }
    }

    pub fn init(&mut self, block_count: usize, block_size: usize, at: Option<&mut [u8]>) {
        self.sema.init(block_count as Uint);
        let mut inner = self.inner.irqsave_lock();
        inner.init(block_count, block_size, at);
    }

    #[inline]
    pub fn init_blocks(&mut self, init: impl Fn(*mut u8)) {
        let mut inner = self.inner.irqsave_lock();
        let mut it = BlockListIterator::new(&inner.free_list, None);
        for mut block in it {
            init(unsafe { block.as_mut().owner_mut().base() });
        }
    }

    pub fn get_block_with_timeout(&self, ticks: usize) -> *mut core::ffi::c_void {
        if irq::is_in_irq() {
            return core::ptr::null_mut();
        }
        let mut ok = false;
        if ticks == 0 {
            ok = self.sema.try_acquire::<InsertToEnd>();
        } else {
            ok = self.sema.acquire_timeout::<InsertToEnd>(ticks);
        }
        if !ok {
            return core::ptr::null_mut();
        }
        let mut inner = self.inner.irqsave_lock();
        let mut it = BlockListIterator::new(&inner.free_list, None);
        let Some(mut node) = it.next() else {
            debug_assert_eq!(inner.free_blocks, 0);
            self.sema.release();
            return core::ptr::null_mut();
        };
        let block = unsafe { node.as_mut().owner_mut() };
        let ok = BlockList::detach(&mut block.node);
        debug_assert!(ok);
        debug_assert!(block.node.is_detached());
        let ok = BlockList::insert_after(&mut inner.busy_list, &mut block.node);
        debug_assert!(ok);
        inner.free_blocks -= 1;
        self.sema.release();
        let ptr = block.base();
        ptr as *mut core::ffi::c_void
    }

    pub fn put_block(&self, block: *mut core::ffi::c_void) -> bool {
        let block = block as *mut u8;
        self.sema.acquire_notimeout::<InsertToEnd>();
        let mut inner = self.inner.irqsave_lock();
        let mut recycled: Option<*mut Block> = None;
        for mut b in BlockListIterator::new(&inner.busy_list, None) {
            unsafe {
                if b.as_ref().owner().storage.base() == block && BlockList::detach(b.as_mut()) {
                    recycled = Some(b.as_mut().owner_mut() as *mut _);
                    break;
                }
            }
        }
        let Some(block_ptr) = recycled else {
            self.sema.release();
            return false;
        };
        let block = unsafe { &mut *block_ptr };
        let ok = BlockList::insert_after(&mut inner.free_list, &mut block.node);
        if ok {
            inner.free_blocks += 1;
        }
        self.sema.release();
        ok
    }

    // We expect user doesn't need the pool any more and all blocks
    // should be put back to the pool.
    pub fn clear(&self) {
        const ALIGN: usize = core::mem::align_of::<Block>();
        let mut inner = self.inner.irqsave_lock();
        debug_assert_eq!(inner.free_blocks, inner.total_blocks);
        let it = BlockListIterator::new(&inner.free_list, None);
        for mut block in it {
            let ok = BlockList::detach(unsafe { block.as_mut() });
            inner.free_blocks -= 1;
            inner.total_blocks -= 1;
            let ptr = unsafe { block.as_mut().owner_mut() };
            unsafe { drop(Box::from_raw(ptr)) };
        }
    }

    pub fn total_blocks(&self) -> usize {
        let inner = self.inner.irqsave_lock();
        inner.total_blocks
    }

    pub fn free_blocks(&self) -> usize {
        let inner = self.inner.irqsave_lock();
        inner.free_blocks
    }

    pub fn block_size(&self) -> usize {
        let inner = self.inner.irqsave_lock();
        inner.block_size
    }

    pub fn dismiss_waiters(&self) -> usize {
        self.sema.reset()
    }
}

impl !Send for MemoryPool {}
unsafe impl Sync for MemoryPool {}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::thread;
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn test_mempool_basic() {
        let mut mp = MemoryPool::new();
        mp.init(4, 512, None);
        assert_eq!(mp.block_size(), 512);
        assert_eq!(mp.total_blocks(), 4);
        assert_eq!(mp.free_blocks(), 4);
        let block = mp.get_block_with_timeout(0);
        assert!(!block.is_null());
        assert_eq!(mp.free_blocks(), 3);
        mp.put_block(block);
        assert_eq!(mp.free_blocks(), 4);
        mp.clear();
        assert_eq!(mp.free_blocks(), 0);
        assert_eq!(mp.total_blocks(), 0);
    }

    #[test]
    fn test_mempool_few_threads() {
        let n = 4;
        let mut mp = Arc::new(MemoryPool::new());
        Arc::get_mut(&mut mp).unwrap().init(n, 1024, None);
        let counter = Arc::new(AtomicUsize::new(0));
        for i in 0..n {
            let mp = mp.clone();
            let counter = counter.clone();
            thread::spawn(move || {
                let block = mp.get_block_with_timeout(1024);
                assert!(!block.is_null());
                mp.put_block(block);
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
        loop {
            if counter.load(Ordering::Relaxed) == n {
                break;
            }
            scheduler::yield_me();
        }
        mp.clear();
    }

    #[test]
    fn test_mempool_many_threads() {
        // Do NOT increase this value greater than 256 while
        // TinyArc on 32-bit has only 8 bits for RC.
        let n = 192;
        let mut mp = Arc::new(MemoryPool::new());
        Arc::get_mut(&mut mp).unwrap().init(n, 64, None);
        let counter = Arc::new(AtomicUsize::new(0));
        for i in 0..n {
            let mp = mp.clone();
            let counter = counter.clone();
            thread::spawn(move || {
                let block = mp.get_block_with_timeout(1024);
                assert!(!block.is_null());
                mp.put_block(block);
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
        loop {
            if counter.load(Ordering::Acquire) == n {
                break;
            }
            scheduler::yield_me();
        }
        assert_eq!(counter.load(Ordering::Relaxed), n);
        mp.clear();
    }

    #[test]
    fn test_try_allocate_from_mempool() {
        let mut mp = MemoryPool::new();
        mp.init(2, 64, None);
        let p0 = mp.get_block_with_timeout(0);
        assert!(!p0.is_null());
        let p1 = mp.get_block_with_timeout(0);
        assert!(!p1.is_null());
        let p2 = mp.get_block_with_timeout(0);
        assert!(p2.is_null());
        assert!(mp.put_block(p0));
        assert!(mp.put_block(p1));
        mp.clear();
    }

    #[test]
    fn test_threaded_try_allocate_from_mempool() {
        let n = 192;
        let mut mp = Arc::new(MemoryPool::new());
        Arc::get_mut(&mut mp).unwrap().init(n, 64, None);
        let counter = Arc::new(AtomicUsize::new(0));
        for i in 0..n {
            let mp = mp.clone();
            let counter = counter.clone();
            thread::spawn(move || {
                let block = mp.get_block_with_timeout(0);
                assert!(!block.is_null());
                assert!(mp.put_block(block));
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
        loop {
            if counter.load(Ordering::Relaxed) == n {
                break;
            }
            scheduler::yield_me();
        }
        assert_eq!(counter.load(Ordering::Relaxed), n);
        mp.clear();
    }
}
