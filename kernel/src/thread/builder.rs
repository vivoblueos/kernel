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
    arch, config, debug, scheduler, static_arc,
    sync::spinlock::{SpinLock, SpinLockGuard},
    thread, trace,
    types::{ArcInner, ArcList, ArcListIterator, IlistHead as ListHead, Uint},
};
use alloc::boxed::Box;
use config::SYSTEM_THREAD_STACK_SIZE;
use core::mem::MaybeUninit;
use thread::{
    AlignedStackStorage, Entry, OffsetOfGlobal, Stack, Thread, ThreadKind, ThreadNode,
    ThreadPriority,
};

type Head = ListHead<Thread, OffsetOfGlobal>;
type ThreadList = ArcList<Thread, OffsetOfGlobal>;

static_arc! {
    GLOBAL_QUEUE(SpinLock<Head>, SpinLock::new(Head::new())),
}

pub(crate) struct GlobalQueueVisitor<'a> {
    lock: SpinLockGuard<'a, Head>,
    it: ArcListIterator<Thread, OffsetOfGlobal>,
}

impl GlobalQueueVisitor<'_> {
    pub fn new() -> Self {
        let lock = GLOBAL_QUEUE.irqsave_lock();
        let it = ArcListIterator::new(&*lock, None);
        Self { lock, it }
    }

    pub fn next(&mut self) -> Option<ThreadNode> {
        self.it.next()
    }

    pub fn add(t: ThreadNode) -> bool {
        let mut w = GLOBAL_QUEUE.irqsave_lock();
        ThreadList::insert_after(&mut *w, t.clone())
    }

    pub fn remove(t: &ThreadNode) -> bool {
        let mut w = GLOBAL_QUEUE.irqsave_lock();
        for mut e in ArcListIterator::new(&*w, None) {
            if Thread::id(&e) == Thread::id(t) {
                return ThreadList::detach(&e);
            }
        }
        false
    }
}

pub fn spawn<F>(f: F) -> Option<ThreadNode>
where
    F: FnOnce() + Send + 'static,
{
    let entry = Box::new(f);
    let builder = Builder::new(Entry::Closure(entry));
    let t = builder.build();
    if scheduler::queue_ready_thread(thread::CREATED, t.clone()) {
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
        let stack = self.stack.take().map_or_else(
            || Stack::Boxed(unsafe { Box::<AlignedStackStorage>::new_uninit().assume_init() }),
            |v| v,
        );
        w.init(stack, self.entry);
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
        scheduler::queue_ready_thread(super::CREATED, t.clone());
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
    pub(crate) const fn const_new(kind: ThreadKind) -> Self {
        Self {
            arc: ArcInner::<Thread>::new(Thread::new(kind)),
            stack: SystemThreadStack {
                rep: [0u8; SYSTEM_THREAD_STACK_SIZE],
            },
        }
    }

    pub(crate) const fn new(kind: ThreadKind) -> Self {
        Self::const_new(kind)
    }
}

pub(crate) fn build_static_thread(
    t: &'static mut MaybeUninit<ThreadNode>,
    // It must be 'static, since the ThreadNode returned doesn't
    // carry lifetime relationship to the SystemThreadStorage.
    s: &'static SystemThreadStorage,
    p: ThreadPriority,
    init_state: Uint,
    entry: Entry,
    kind: ThreadKind,
) -> ThreadNode {
    let inner = &s.arc;
    let stack = &s.stack;
    let arc = unsafe { ThreadNode::const_new(inner) };
    assert_eq!(ThreadNode::strong_count(&arc), 1);
    let _id = Thread::id(&arc);
    let mut w = arc.lock();
    w.init(
        Stack::Raw {
            base: stack.rep.as_ptr() as usize,
            size: stack.rep.len(),
        },
        entry,
    );
    w.set_priority(p);
    w.set_kind(kind);
    assert!((thread::CREATED..=thread::RETIRED).contains(&init_state));
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
