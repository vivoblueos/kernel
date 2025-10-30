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

// Asynk contains a simple executor, however runs fast.

extern crate alloc;
use crate::{
    config::MAX_THREAD_PRIORITY,
    scheduler, static_arc,
    support::ArcBufferingQueue,
    sync::{atomic_wait, ISpinLock, SpinLockGuard},
    thread::{self, Entry, SystemThreadStorage, ThreadKind, ThreadNode},
    types::{impl_simple_intrusive_adapter, Arc, IlistHead},
};
use alloc::boxed::Box;
use core::{
    future::Future,
    mem::MaybeUninit,
    pin::Pin,
    sync::atomic::{AtomicUsize, Ordering},
    task::{Context, Poll, Waker},
};

impl_simple_intrusive_adapter!(TaskletNode, Tasklet, node);
impl_simple_intrusive_adapter!(TaskletLock, Tasklet, lock);

pub struct Tasklet {
    node: IlistHead<Tasklet, TaskletNode>,
    lock: ISpinLock<Tasklet, TaskletLock>,
    future: Pin<Box<dyn Future<Output = ()>>>,
    blocked: Option<ThreadNode>,
}

impl Tasklet {
    pub fn new(future: Pin<Box<dyn Future<Output = ()>>>) -> Self {
        Self {
            node: IlistHead::new(),
            future,
            lock: ISpinLock::new(),
            blocked: None,
        }
    }

    pub fn lock(&self) -> SpinLockGuard<'_, Tasklet> {
        self.lock.irqsave_lock()
    }
}

type AsyncWorkQueue = ArcBufferingQueue<Tasklet, TaskletNode, 2>;
static mut POLLER_STORAGE: SystemThreadStorage = SystemThreadStorage::new(ThreadKind::AsyncPoller);
static mut POLLER: MaybeUninit<ThreadNode> = MaybeUninit::zeroed();
static POLLER_WAKER: AtomicUsize = AtomicUsize::new(0);
static_arc! {
    ASYNC_WORK_QUEUE(AsyncWorkQueue, AsyncWorkQueue::new()),
}

pub(crate) fn init() {
    ASYNC_WORK_QUEUE.init_queues();
    let poller = thread::build_static_thread(
        unsafe { &mut POLLER },
        unsafe { &mut POLLER_STORAGE },
        MAX_THREAD_PRIORITY,
        thread::CREATED,
        Entry::C(poll),
        ThreadKind::AsyncPoller,
    );
    let ok = scheduler::queue_ready_thread(thread::CREATED, poller);
    debug_assert!(ok);
}

fn create_tasklet(future: impl Future<Output = ()> + 'static) -> Arc<Tasklet> {
    let future = Box::pin(future);
    Arc::new(Tasklet::new(future))
}

pub fn block_on(future: impl Future<Output = ()> + Send + 'static) {
    let t = scheduler::current_thread();
    let mut task = create_tasklet(future);
    task.lock().blocked = Some(t.clone());
    scheduler::suspend_me_with_hook(move || {
        let ok = t.transfer_state(thread::RUNNING, thread::SUSPENDED);
        assert!(ok);
        enqueue_active_tasklet(task);
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "[TH:0x{:x}] is waking up the poller",
            scheduler::current_thread_id()
        );
        wake_poller();
    });
}

fn wake_poller() {
    POLLER_WAKER.fetch_add(1, Ordering::Release);
    atomic_wait::atomic_wake(&POLLER_WAKER, 1);
}

pub fn spawn(future: impl Future<Output = ()> + Send + 'static) -> Arc<Tasklet> {
    let task = create_tasklet(future);
    enqueue_active_tasklet(task.clone());
    wake_poller();
    task
}

pub fn enqueue_active_tasklet(t: Arc<Tasklet>) {
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] is enqueuing tasklet",
        scheduler::current_thread_id()
    );
    let mut q = ASYNC_WORK_QUEUE.get_active_queue();
    let _guard = t.lock();
    q.push_back(t.clone());
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] has enqueued tasklet",
        scheduler::current_thread_id()
    );
}

fn poll_inner() {
    let mut ctx = Context::from_waker(Waker::noop());
    let mut w = ASYNC_WORK_QUEUE.advance_active_queue();
    for mut task in w.iter() {
        let mut l = task.lock();
        if let Poll::Ready(()) = l.future.as_mut().poll(&mut ctx) {
            if let Some(t) = l.blocked.take() {
                scheduler::queue_ready_thread(thread::SUSPENDED, t);
            }
            // If we detach the task what ever it's ready or
            // pending, it would be edge-level triggered. Now
            // we're using level-trigger mode conservatively.
            AsyncWorkQueue::WorkList::detach(&mut task.clone());
        } else {
            // FIXME: This is not an efficient impl right now. We
            // might need a waker for each future, so that the poller
            // doesn't need to poll all futures when woken up.
        }
    }
}

extern "C" fn poll() {
    loop {
        let n = POLLER_WAKER.load(Ordering::Acquire);
        poll_inner();
        atomic_wait::atomic_wait(&POLLER_WAKER, n, None);
    }
}
