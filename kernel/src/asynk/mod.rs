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
    scheduler,
    scheduler::WaitQueue,
    static_arc,
    support::ArcBufferingQueue,
    sync::{atomic_wait, ISpinLock, SpinLockGuard},
    thread::{self, Entry, SystemThreadStorage, ThreadKind, ThreadNode},
    time::Tick,
    types::{impl_simple_intrusive_adapter, Arc, IlistHead},
};
use alloc::boxed::Box;
use core::{
    future::Future,
    mem::MaybeUninit,
    pin::Pin,
    sync::atomic::{AtomicUsize, Ordering},
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

impl_simple_intrusive_adapter!(TaskletNode, Tasklet, node);
impl_simple_intrusive_adapter!(TaskletLock, Tasklet, lock);

pub struct Tasklet {
    node: IlistHead<Tasklet, TaskletNode>,
    lock: ISpinLock<Tasklet, TaskletLock>,
    future: Pin<Box<dyn Future<Output = ()>>>,
    blocked: Option<ThreadNode>,
    state: AtomicUsize,
}

impl Tasklet {
    pub fn new(future: Pin<Box<dyn Future<Output = ()>>>) -> Self {
        Self {
            node: IlistHead::new(),
            future,
            lock: ISpinLock::new(),
            blocked: None,
            state: AtomicUsize::new(TASKLET_IDLE),
        }
    }

    pub fn lock(&self) -> SpinLockGuard<'_, Tasklet> {
        self.lock.irqsave_lock()
    }
}

type AsyncWorkQueue = ArcBufferingQueue<Tasklet, TaskletNode, 2>;
const TASKLET_IDLE: usize = 0;
const TASKLET_QUEUED: usize = 1;
const TASKLET_POLLING: usize = 2;
const TASKLET_WOKEN: usize = 3;
const TASKLET_COMPLETED: usize = 4;

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
        thread::IDLE,
        Entry::C(poll),
        ThreadKind::AsyncPoller,
    );
    let ok = scheduler::queue_ready_thread(thread::IDLE, poller);
    debug_assert_eq!(ok, Ok(()));
}

fn create_tasklet(future: impl Future<Output = ()> + 'static) -> Arc<Tasklet> {
    let future = Box::pin(future);
    Arc::new(Tasklet::new(future))
}

pub fn block_on(future: impl Future<Output = ()> + Send + 'static) {
    let t = scheduler::current_thread();
    let task = create_tasklet(future);
    let mut w = task.lock();
    w.blocked = Some(t.clone());
    t.disable_preempt();
    wake_tasklet(task.clone());
    scheduler::suspend_me_for::<Tasklet>(Tick::MAX, Some(w));
    t.enable_preempt();
}

fn wake_poller() {
    POLLER_WAKER.fetch_add(1, Ordering::Release);
    atomic_wait::atomic_wake(&POLLER_WAKER, 1);
}

pub fn spawn(future: impl Future<Output = ()> + Send + 'static) -> Arc<Tasklet> {
    let task = create_tasklet(future);
    wake_tasklet(task.clone());
    task
}

pub fn enqueue_active_tasklet(t: Arc<Tasklet>) {
    wake_tasklet(t);
}

fn enqueue_queued_tasklet(t: Arc<Tasklet>) {
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] is enqueuing tasklet",
        scheduler::current_thread_id()
    );
    let mut q = ASYNC_WORK_QUEUE.get_active_queue();
    let ok = q.push_back(t);
    debug_assert!(ok);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] has enqueued tasklet",
        scheduler::current_thread_id()
    );
}

fn wake_tasklet(task: Arc<Tasklet>) {
    loop {
        match task.state.load(Ordering::Acquire) {
            TASKLET_IDLE => {
                if task
                    .state
                    .compare_exchange(
                        TASKLET_IDLE,
                        TASKLET_QUEUED,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    enqueue_queued_tasklet(task);
                    wake_poller();
                    return;
                }
            }
            TASKLET_POLLING => {
                if task
                    .state
                    .compare_exchange(
                        TASKLET_POLLING,
                        TASKLET_WOKEN,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    return;
                }
            }
            TASKLET_QUEUED | TASKLET_WOKEN | TASKLET_COMPLETED => return,
            _ => unreachable!(),
        }
    }
}

fn tasklet_waker_vtable() -> &'static RawWakerVTable {
    &RawWakerVTable::new(
        |data| {
            let task = unsafe { Arc::from_raw(data as *const Tasklet) };
            let cloned = task.clone();
            core::mem::forget(task);
            RawWaker::new(Arc::into_raw(cloned) as *const (), tasklet_waker_vtable())
        },
        |data| {
            let task = unsafe { Arc::from_raw(data as *const Tasklet) };
            wake_tasklet(task);
        },
        |data| {
            let task = unsafe { Arc::from_raw(data as *const Tasklet) };
            let cloned = task.clone();
            core::mem::forget(task);
            wake_tasklet(cloned);
        },
        |data| {
            let _ = unsafe { Arc::from_raw(data as *const Tasklet) };
        },
    )
}

fn tasklet_waker(task: Arc<Tasklet>) -> Waker {
    let raw_waker = RawWaker::new(Arc::into_raw(task) as *const (), tasklet_waker_vtable());
    unsafe { Waker::from_raw(raw_waker) }
}

fn finish_pending_poll(task: Arc<Tasklet>) {
    match task.state.compare_exchange(
        TASKLET_POLLING,
        TASKLET_IDLE,
        Ordering::AcqRel,
        Ordering::Acquire,
    ) {
        Ok(_) => {}
        Err(TASKLET_WOKEN) => {
            task.state.store(TASKLET_QUEUED, Ordering::Release);
            enqueue_queued_tasklet(task);
            wake_poller();
        }
        Err(state) => unreachable!("unexpected tasklet state after poll: {}", state),
    }
}

fn poll_inner() {
    loop {
        let Some(task) = ({
            let mut w = ASYNC_WORK_QUEUE.advance_active_queue();
            w.pop_front()
        }) else {
            break;
        };

        let old = task.state.compare_exchange(
            TASKLET_QUEUED,
            TASKLET_POLLING,
            Ordering::AcqRel,
            Ordering::Acquire,
        );
        debug_assert_eq!(old, Ok(TASKLET_QUEUED));

        let waker = tasklet_waker(task.clone());
        let mut ctx = Context::from_waker(&waker);
        let mut l = task.lock();
        match l.future.as_mut().poll(&mut ctx) {
            Poll::Ready(()) => {
                task.state.store(TASKLET_COMPLETED, Ordering::Release);
                let blocked = l.blocked.take();
                drop(l);
                if let Some(t) = blocked {
                    let ok = scheduler::queue_ready_thread(thread::SUSPENDED, t);
                    debug_assert_eq!(ok, Ok(()));
                }
            }
            Poll::Pending => {
                drop(l);
                finish_pending_poll(task);
            }
        }
    }
}

extern "C" fn poll() {
    loop {
        let n = POLLER_WAKER.load(Ordering::Acquire);
        poll_inner();
        atomic_wait::atomic_wait(&POLLER_WAKER, n, Tick::MAX);
    }
}

pub fn yield_now() -> impl Future<Output = ()> {
    YieldNow { polled: false }
}

struct YieldNow {
    polled: bool,
}

impl Future for YieldNow {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.polled {
            Poll::Ready(())
        } else {
            let waker = cx.waker().clone();
            waker.wake_by_ref();
            self.get_mut().polled = true;
            Poll::Pending
        }
    }
}
