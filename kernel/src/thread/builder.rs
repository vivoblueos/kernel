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

extern crate alloc;

use crate::{
    arch,
    arch::Context,
    config, debug, scheduler, static_arc,
    support::Storage,
    sync::spinlock::{SpinLock, SpinLockGuard},
    thread, trace,
    types::{
        Arc, ArcInner, ArcList, ArcListIterator, AtomicIlistHead as ListHead, StaticListOwner, Uint,
    },
};
use alloc::boxed::Box;
use config::{DEFAULT_STACK_SIZE, SYSTEM_THREAD_STACK_SIZE};
use core::{alloc::Layout, mem::MaybeUninit};
use thread::{
    Entry, GlobalQueueListHead, OffsetOfGlobal, Stack, Thread, ThreadKind, ThreadNode,
    ThreadPriority,
};

type Head = ListHead<Thread, OffsetOfGlobal>;
type ThreadList = ArcList<Thread, OffsetOfGlobal>;

static_arc! {
    GLOBAL_QUEUE(SpinLock<Head>, SpinLock::new(Head::new())),
}

pub struct GlobalQueueVisitor<'a> {
    lock: SpinLockGuard<'a, Head>,
    it: ArcListIterator<'a, Thread, OffsetOfGlobal>,
}

#[derive(Default, Debug)]
pub(crate) struct GlobalQueue;

impl const StaticListOwner<Thread, OffsetOfGlobal> for GlobalQueue {
    fn get() -> &'static Arc<SpinLock<Head>> {
        &GLOBAL_QUEUE
    }
}

impl GlobalQueueVisitor<'_> {
    pub fn new() -> Self {
        let lock = GLOBAL_QUEUE.irqsave_lock();
        let it = ArcListIterator::new(&*lock, None);
        Self { lock, it }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<ThreadNode> {
        Some(unsafe { Arc::clone_from(self.it.next()?) })
    }

    pub fn add(t: ThreadNode) -> bool {
        GlobalQueueListHead::insert(t)
    }

    pub fn remove(t: &mut ThreadNode) -> bool {
        GlobalQueueListHead::detach(t)
    }

    pub fn find_if<F>(mut predicate: F) -> Option<ThreadNode>
    where
        F: FnMut(&ThreadNode) -> bool,
    {
        let mut visitor = GlobalQueueVisitor::new();
        while let Some(t) = visitor.next() {
            if predicate(&t) {
                return Some(t);
            }
        }
        None
    }
}

pub fn spawn<F>(f: F) -> Option<ThreadNode>
where
    F: FnOnce() + Send + 'static,
{
    let entry = Box::new(f);
    let builder = Builder::new(Entry::Closure(entry));
    let t = builder.build();
    if scheduler::queue_ready_thread(thread::IDLE, t.clone()) {
        return Some(t);
    }
    None
}

pub struct Builder {
    stack: Option<Stack>,
    entry: Entry,
    priority: ThreadPriority,
}

impl Builder {
    pub fn new(entry: Entry) -> Self {
        Self {
            stack: None,
            entry,
            priority: config::MAX_THREAD_PRIORITY / 2,
        }
    }

    #[inline]
    pub fn set_priority(mut self, p: ThreadPriority) -> Self {
        self.priority = p;
        self
    }

    #[inline]
    pub fn set_stack(mut self, stack: Stack) -> Self {
        self.stack = Some(stack);
        self
    }

    pub fn build(mut self) -> ThreadNode {
        let thread = ThreadNode::new(Thread::new(ThreadKind::Normal));
        let mut w = thread.lock();
        let stack = self
            .stack
            .take()
            .map_or_else(|| Stack::from_size(DEFAULT_STACK_SIZE), |v| v);
        w.init(stack, self.entry);
        w.set_origin_priority(self.priority);
        w.set_priority(self.priority);
        drop(w);
        GlobalQueueVisitor::add(thread.clone());

        #[cfg(procfs)]
        {
            let _ = crate::vfs::trace_thread_create(thread.clone());
        }

        thread
    }

    pub fn start(self) -> ThreadNode {
        let t = self.build();
        let ok = scheduler::queue_ready_thread(super::IDLE, t.clone());
        debug_assert!(ok);
        // TODO: Invoke yield_me_now_or_later for better realtime performance. However
        // this breaks some existed tests and need TBI.
        t
    }
}

#[repr(align(16))]
#[derive(Copy, Clone, Debug)]
pub(crate) struct SystemThreadStack {
    pub(crate) rep: [u8; SYSTEM_THREAD_STACK_SIZE],
}

#[derive(Debug)]
pub(crate) struct SystemThreadStorage {
    pub(crate) arc: ArcInner<Thread>,
    pub(crate) stack: SystemThreadStack,
}

impl SystemThreadStorage {
    pub(crate) const fn new(kind: ThreadKind) -> Self {
        Self {
            arc: ArcInner::<Thread>::new(Thread::new(kind)),
            stack: SystemThreadStack {
                rep: [0u8; SYSTEM_THREAD_STACK_SIZE],
            },
        }
    }
}

pub(crate) fn build_static_thread(
    t: &'static mut MaybeUninit<ThreadNode>,
    // It must be 'static, since the ThreadNode returned doesn't
    // carry lifetime relationship to the SystemThreadStorage.
    s: &'static mut SystemThreadStorage,
    p: ThreadPriority,
    init_state: Uint,
    entry: Entry,
    kind: ThreadKind,
) -> ThreadNode {
    let inner = &s.arc;
    let stack = &mut s.stack;
    let arc = unsafe { ThreadNode::from_static_inner_ref(inner) };
    debug_assert_eq!(ThreadNode::strong_count(&arc), 1);
    let _id = Thread::id(&arc);
    let mut w = arc.lock();
    w.init(
        Stack::from_raw(stack.rep.as_mut_ptr(), stack.rep.len()),
        entry,
    );
    w.set_origin_priority(p);
    w.set_priority(p);
    w.set_kind(kind);
    debug_assert!((thread::IDLE..=thread::RETIRED).contains(&init_state));
    unsafe { w.set_state(init_state) };
    debug!(
        "System thread 0x{:x} created: sp: 0x{:x}, stack base: {:?}, stack size: {}, context size: {}",
        id,
        w.saved_sp(),
        stack.rep.as_ptr(),
        stack.rep.len(),
        core::mem::size_of::<arch::Context>(),
    );
    drop(w);
    t.write(arc.clone());
    GlobalQueueVisitor::add(arc.clone());
    arc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sync::ConstBarrier;
    use blueos_test_macro::test;
    use core::alloc::Layout;

    #[test]
    fn test_use_alloc_stack() {
        const SIZE: usize = 1600;
        const ALIGN: usize = 8;
        let layout = Layout::from_size_align(SIZE, ALIGN).unwrap();
        let base = unsafe { alloc::alloc::alloc(layout) };
        assert!(!base.is_null());
        let stack = Stack::from_storage(Storage::Alloc(base, layout));
        let sync_me = Arc::new(ConstBarrier::<{ 2 }>::new());
        let sync_other = sync_me.clone();
        let _other = Builder::new(Entry::Closure(Box::new(move || {
            let current = scheduler::current_thread();
            assert_eq!(current.stack_size(), SIZE);
            sync_other.wait()
        })))
        .set_stack(stack)
        .start();
        sync_me.wait();
    }
}
