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

// This mutex implementation is basically following
// https://adastra-soft.com/priority-inheritance-mutex-algorithm/
// https://linuxdevices.org/ldfiles/misc/yodaiken-july02.pdf
//
// The implementation heavily relies on this invariance:
// When Mutex's inner spinlock is acquired and its owner is Non-None, the
// owner's `post` operation, in which `recover_priority` is performed, is
// anticipated. The net effect is when a thread is holding no mutex, its
// priority == its origin_priority.
//
// The implementation doesn't use nested critical region to ensure global
// consistency, instead it utilizes a local approach, while keeping the above
// invariance, to achieve a not bad result.

use super::{SpinLock, SpinLockGuard};
use crate::{
    irq,
    scheduler::{self, wait_queue, InsertMode, OffsetOfWait, WaitEntry, WaitQueue},
    thread::{self, Thread, ThreadNode},
    time::{NO_WAITING, WAITING_FOREVER},
    types::{
        impl_simple_intrusive_adapter, Arc, ArcCas, ArcList, GenericList, ThreadPriority, Uint,
    },
};
use alloc::string::String;
use core::{
    cell::{Cell, UnsafeCell},
    ops::Deref,
    sync::atomic::{AtomicU32, Ordering},
};

impl_simple_intrusive_adapter!(OffsetOfMutexNode, Mutex, mutex_node);
pub(crate) type MutexList = ArcList<Mutex, OffsetOfMutexNode>;
pub(crate) type MutexListIterator = <MutexList as GenericList>::Iter;
type MutexNode = <MutexList as GenericList>::Node;

const CHAIN_LENGTH_LIMIT: usize = 4;

#[derive(Debug)]
pub struct Mutex {
    // We let the Spinlock protect the whole Mutex. Sort threads by priority.
    pending: SpinLock<WaitQueue>,
    nesting_count: Cell<Uint>,
    owner: ArcCas<Thread>,
    mutex_node: MutexNode,
}

impl Mutex {
    pub const fn new() -> Self {
        Self {
            pending: SpinLock::new(WaitQueue::new()),
            nesting_count: Cell::new(0),
            owner: ArcCas::new(None),
            mutex_node: MutexNode::new(),
        }
    }

    pub fn init(&self) -> bool {
        self.pending.irqsave_lock().init()
    }

    pub fn waitqueue_guard(&self) -> SpinLockGuard<'_, ArcList<WaitEntry, OffsetOfWait>> {
        self.pending.irqsave_lock()
    }

    pub fn count(&self) -> Uint {
        let _w = self.pending.irqsave_lock();
        self.nesting_count.get()
    }

    #[inline]
    fn nesting_count(&self) -> Uint {
        self.nesting_count.get()
    }

    #[inline]
    fn increment_nesting_count(&self) -> Uint {
        let old = self.nesting_count.get();
        self.nesting_count.set(old + 1);
        old
    }

    #[inline]
    fn decrement_nesting_count(&self) -> Uint {
        let old = self.nesting_count.get();
        self.nesting_count.set(old - 1);
        old
    }

    #[inline]
    fn replace_owner(&self, t: Option<ThreadNode>) -> Option<ThreadNode> {
        self.owner.swap(t, Ordering::Release)
    }

    #[inline]
    pub fn owner(&self) -> Option<ThreadNode> {
        self.owner.load(Ordering::Acquire)
    }

    pub fn create() -> Arc<Self> {
        let mutex = Arc::new(Self::new());
        mutex.init();
        mutex
    }

    pub fn pend_for(&self, mut ticks: usize) -> bool {
        assert!(!irq::is_in_irq());
        let this_thread = scheduler::current_thread();
        let this_mutex = unsafe { MutexList::make_arc_from(&self.mutex_node) };
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "[PEND_FOR] TH:0x{:x} is getting the spinlock of mutex {:?}",
            Thread::id(&this_thread),
            self as *const _
        );
        let mut w = self.pending.irqsave_lock();
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "[PEND_FOR] TH:0x{:x} has got the spinlock of mutex {:?}",
            Thread::id(&this_thread),
            self as *const _
        );

        let mut last_sys_ticks = crate::time::get_sys_ticks();
        loop {
            if self.nesting_count() == 0 {
                self.increment_nesting_count();
                let old = self.replace_owner(Some(this_thread.clone()));
                debug_assert!(old.is_none());
                let mut guard = this_thread.lock();
                let ok = guard.add_acquired_mutex(this_mutex.clone());
                debug_assert!(ok);
                let _ = guard.replace_pending_on_mutex(None);
                #[cfg(debugging_scheduler)]
                crate::trace!(
                    "TH:0x{:x} @ P{} has got mutex {:?}",
                    Thread::id(&this_thread),
                    this_thread.priority(),
                    self as *const _
                );
                return true;
            }

            let Some(owner) = self.owner() else {
                panic!("When nesting count > 0, this mutex should be owned by a thread")
            };

            if Arc::is(&owner, &this_thread) {
                self.increment_nesting_count();
                return true;
            }

            if ticks == NO_WAITING {
                this_thread.replace_pending_on_mutex(None);
                Self::recover_priority(&this_thread, &this_mutex);
                return false;
            }

            #[cfg(debugging_scheduler)]
            crate::trace!(
                "TH:0x{:x} @ P{} is entering inner mutex {:?}",
                Thread::id(&this_thread),
                this_thread.priority(),
                self as *const _
            );

            let timeout = Self::inner_pend_for(ticks, &this_mutex, w, &this_thread, &owner);
            if timeout {
                this_thread.replace_pending_on_mutex(None);
                Self::recover_priority(&this_thread, &this_mutex);
                return false;
            }

            let now = crate::time::get_sys_ticks();
            let elapsed_ticks = now - last_sys_ticks;
            if elapsed_ticks >= ticks {
                ticks = 0;
            } else {
                ticks -= elapsed_ticks;
            }
            last_sys_ticks = now;

            w = self.pending.irqsave_lock();
        }
    }

    fn inner_pend_for(
        ticks: usize,
        this_mutex: &Arc<Self>,
        this_lock: SpinLockGuard<'_, WaitQueue>,
        this_thread: &ThreadNode,
        owner_thread: &ThreadNode,
    ) -> bool {
        let this_priority = this_thread.priority();
        // We walk along the blocking chain to scan no more than
        // CHAIN_LENGTH_LIMIT threads.
        let mut current_len = 0;
        let mut scanning_thread = owner_thread.clone();
        // `this_lock` should guarantee `promote_priority_to` happens-before
        // `recover_priority`. That's to say, when we are seeing the owner of
        // this mutex after spinlock this mutex, the owner hasn't run `post` yet
        // and `recover_priority` is anticipated. This should also appply to
        // others.
        //
        // Imagine we have a mutex chain, ( => stands for 'owned by', -> stands
        // for 'pending on') this_mutex => owner_thread -> m0 => t0 -> m1 => t1.
        // Whenever we meet a new mutex, we try to spinlock the mutex and
        // inspect its owner. After inspect its owner, we spinunlock the mutex
        // and spinlock the next mutex. The spinlock of this_mutex is kept being
        // held by this_thread during walking along this chain.
        let mut other_mutex = None;
        let mut other_lock = None;
        while current_len < CHAIN_LENGTH_LIMIT {
            current_len += 1;
            // We are holding the mutex's spinlock and the scanning thread is
            // its owner. It's safe to promote scanning thread's priority.
            let ok = scanning_thread.lock().promote_priority_to(this_priority);
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "TH:0x{:x} is promoting TH:0x{:x} to {}, succ? {}",
                Thread::id(this_thread),
                Thread::id(&scanning_thread),
                this_priority,
                ok,
            );

            // TODO: If the scanning thread is in the ready queue, we can
            // promote it to a higher priority queue.
            other_lock = None;
            other_mutex = scanning_thread.pending_on_mutex();
            let Some(other_mutex_ref) = &other_mutex else {
                break;
            };
            if Arc::is(this_mutex, other_mutex_ref) {
                panic!("Cycle mutex deteced!");
            }
            other_lock = Some(other_mutex_ref.pending.irqsave_lock());
            let Some(other_lock_ref) = &mut other_lock else {
                break;
            };
            // Adjust the position of the scanning thread in the WaitQueue.
            if !Self::adjust_wait_queue_position_by(
                this_priority,
                &scanning_thread,
                &other_mutex_ref.clone(),
                other_lock_ref,
            ) {
                break;
            }
            let Some(other_thread) = other_mutex_ref.owner() else {
                break;
            };
            scanning_thread = other_thread;
        }
        drop(other_lock);
        drop(other_mutex);
        // FIXME: For current implementation, there is a small time window
        // that we have seen the pending_on_mutex, however it's not in the
        // WaitQueue.
        let old = this_thread.replace_pending_on_mutex(Some(this_mutex.clone()));
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "TH:0x{:x} is pending on mutex {:?}",
            Thread::id(this_thread),
            this_mutex.deref() as *const _,
        );
        if let Some(check) = &old {
            debug_assert!(Arc::is(check, this_mutex));
        };
        drop(old);
        scheduler::suspend_me_with_timeout(this_lock, ticks, InsertMode::InsertByPrio)
    }

    fn adjust_wait_queue_position_by(
        target_prio: ThreadPriority,
        who: &ThreadNode,
        mutex: &Arc<Self>,
        mutex_lock: &mut SpinLockGuard<'_, WaitQueue>,
    ) -> bool {
        let Some(pending_on_mutex) = who.pending_on_mutex() else {
            return false;
        };
        if !Arc::is(mutex, &pending_on_mutex) {
            return false;
        }
        let mut entry = None;
        for e in mutex_lock.iter() {
            if Arc::is(&e.thread, who) {
                entry = Some(e);
                break;
            }
        }
        let Some(mut entry) = entry else {
            return false;
        };
        // The entry only belongs to this Mutex so that we don't need to scan
        // the whole queue.
        if !WaitQueue::detach(&mut entry) {
            return false;
        }
        mutex_lock.push_by(wait_queue::compare_priority, entry)
    }

    pub fn post(&self) {
        assert!(!irq::is_in_irq());
        let this_thread = scheduler::current_thread();
        {
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "TH:0x{:x} is getting the spinlock of mutex {:?}",
                Thread::id(&this_thread),
                self as *const _
            );
            let mut this_lock = self.pending.irqsave_lock();
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "TH:0x{:x} has got the spinlock of mutex {:?}",
                Thread::id(&this_thread),
                self as *const _
            );
            let Some(owner) = self.owner() else {
                assert_eq!(self.nesting_count(), 0);
                log::warn!("The mutex is free, should not be released");
                return;
            };
            assert_eq!(Thread::id(&owner), Thread::id(&this_thread));
            if self.decrement_nesting_count() > 1 {
                return;
            }
            let mut this_mutex = unsafe { MutexList::make_arc_from(&self.mutex_node) };
            while let Some(next) = this_lock.pop_front() {
                let t = next.thread.clone();
                if let Some(timer) = &t.timer {
                    timer.stop();
                }
                if scheduler::queue_ready_thread(thread::SUSPENDED, t.clone()) {
                    break;
                }
            }
            {
                let ok = this_thread.remove_acquired_mutex(&this_mutex);
                debug_assert!(ok);
                #[cfg(debugging_scheduler)]
                crate::trace!(
                    "TH:0x{:x} has removed acquired mutex {:?}",
                    Thread::id(&this_thread),
                    self as *const _
                );
                let prio = Self::recover_priority(&this_thread, &this_mutex);
                #[cfg(debugging_scheduler)]
                crate::trace!(
                    "TH:0x{:x} has recover priority to {}",
                    Thread::id(&this_thread),
                    prio,
                );
            }
            self.replace_owner(None);
        }
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "TH:0x{:x} has released mutex {:?}",
            Thread::id(&this_thread),
            self as *const _
        );
        drop(this_thread);
        scheduler::yield_me_now_or_later();
    }

    // Return this thread's previous priority.
    fn recover_priority(this_thread: &ThreadNode, this_mutex: &Arc<Self>) -> ThreadPriority {
        let old_prio = this_thread.priority();
        if !this_thread.has_acquired_mutex() {
            this_thread.lock().recover_priority();
            return old_prio;
        }
        let mut limit = 0;
        let mut prio = old_prio;
        for (limit, mutex) in this_thread.acquired_mutexes_mut().iter().enumerate() {
            if limit >= CHAIN_LENGTH_LIMIT {
                break;
            }
            assert!(!Arc::is(&mutex, this_mutex));
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "Trying to get read lock of mutex {:?}, estimated R {}, W {}",
                mutex.deref() as *const _,
                mutex.pending.reader_count(),
                mutex.pending.writer_count(),
            );
            let read = mutex.pending.irqsave_read();
            #[cfg(debugging_scheduler)]
            crate::trace!("Got the read lock of mutex {:?}", mutex.deref() as *const _);
            let Some(front) = read.front() else {
                continue;
            };
            prio = core::cmp::min(prio, front.thread.priority());
        }
        let _ = this_thread.lock().promote_priority_to(prio);
        old_prio
    }
}

impl Default for Mutex {
    fn default() -> Self {
        Mutex::new()
    }
}

impl !Send for Mutex {}
unsafe impl Sync for Mutex {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{scheduler, thread, time};
    use alloc::{boxed::Box, vec, vec::Vec};
    use blueos_test_macro::{only_test, test};
    use core::sync::atomic::{AtomicUsize, Ordering};

    fn spin_until(target: usize, clock: &AtomicUsize) {
        while clock.load(Ordering::Relaxed) < target {
            #[cfg(target_pointer_width = "32")]
            scheduler::suspend_me_for(8);
            #[cfg(target_pointer_width = "64")]
            scheduler::yield_me();
            core::hint::spin_loop();
        }
    }

    #[test]
    fn test_mutex_new() {
        // Test successful creation with valid counter
        let mutex = Mutex::new();
        assert_eq!(mutex.nesting_count(), 0);

        let mutex1 = Mutex::new();
        assert_eq!(mutex1.nesting_count(), 0);
    }

    #[test]
    fn test_mutex_init() {
        let mutex = Mutex::new();

        // Test initialization
        let result = mutex.init();
        assert!(result);

        // Test multiple initializations
        let result2 = mutex.init();
        assert!(!result2);
    }

    #[test]
    fn test_mutex_pend_post_success() {
        let mutex = Mutex::create();

        // Test successful pend
        let result = mutex.pend_for(WAITING_FOREVER);
        assert!(result);
        assert_eq!(mutex.nesting_count(), 1);

        // post operations
        mutex.post();
        assert_eq!(mutex.nesting_count(), 0);

        // pend
        let result = mutex.pend_for(WAITING_FOREVER);
        assert!(result);
        assert_eq!(mutex.nesting_count(), 1);

        // post operations
        mutex.post();
        assert_eq!(mutex.nesting_count(), 0);
    }

    #[test]
    fn test_mutex_multi_pend_success() {
        let mutex = Mutex::create();

        // Test successful pend
        let result = mutex.pend_for(WAITING_FOREVER);
        assert!(result);
        assert_eq!(mutex.nesting_count(), 1);

        // pend operations
        assert!(mutex.pend_for(WAITING_FOREVER));
        assert_eq!(mutex.nesting_count(), 2);
        mutex.post();
        mutex.post();
    }

    #[test]
    fn test_mutex_multi_pend_post_success() {
        let mutex = Mutex::create();

        // Test 10x pend operations
        for i in 0..10 {
            let result = mutex.pend_for(10);
            assert!(result);
            assert_eq!(mutex.nesting_count(), i + 1);
        }

        // test 10x post operations
        for i in 0..10 {
            assert_eq!(mutex.nesting_count(), 10 - i);
            mutex.post();
        }
        assert_eq!(mutex.nesting_count(), 0);

        // Test 10x pend operations again
        for i in 0..10 {
            let result = mutex.pend_for(10);
            assert!(result);
            assert_eq!(mutex.nesting_count(), i + 1);
        }

        // test 10x post operations
        for i in 0..10 {
            assert_eq!(mutex.nesting_count(), 10 - i);
            mutex.post();
        }
        assert_eq!(mutex.nesting_count(), 0);
    }

    #[test]
    fn test_mutex_multi_thread1() {
        let mutex = Mutex::create();

        let mutex_consumer = mutex.clone();
        let pend_flag = Arc::new(AtomicUsize::new(0));
        let pend_flag_clone = pend_flag.clone();

        let consumer = thread::spawn(move || {
            spin_until(1, &pend_flag_clone);
            assert_eq!(mutex_consumer.nesting_count(), 1);
            pend_flag_clone.store(2, Ordering::Relaxed);
            mutex_consumer.pend_for(10);
            assert_eq!(mutex_consumer.nesting_count(), 1);
            mutex_consumer.post();
            pend_flag_clone.fetch_add(1, Ordering::SeqCst);
        });
        mutex.pend_for(10);
        assert_eq!(mutex.nesting_count(), 1);
        pend_flag.store(1, Ordering::SeqCst);
        spin_until(2, &pend_flag);
        mutex.post();
        while pend_flag.load(Ordering::SeqCst) == 1 {}
    }

    #[test]
    fn test_mutex_multi_thread_nowaiting() {
        let mutex = Mutex::create();

        let mutex_consumer = mutex.clone();
        let pend_flag = Arc::new(AtomicU32::new(0));
        let pend_flag_clone = pend_flag.clone();

        let consumer = thread::spawn(move || {
            while pend_flag_clone.load(Ordering::SeqCst) == 0 {
                scheduler::yield_me();
            }

            assert_eq!(mutex_consumer.nesting_count(), 1);
            let result = mutex_consumer.pend_for(NO_WAITING);
            assert!(!result);
            pend_flag_clone.fetch_add(1, Ordering::SeqCst);
        });
        mutex.pend_for(10);
        assert_eq!(mutex.nesting_count(), 1);
        pend_flag.fetch_add(1, Ordering::SeqCst);
        while pend_flag.load(Ordering::SeqCst) == 1 {
            scheduler::yield_me();
        }
        mutex.post();
    }

    #[test]
    fn test_mutex_multi_thread_timeout() {
        let mutex = Mutex::create();

        let mutex_consumer = mutex.clone();
        let pend_flag = Arc::new(AtomicU32::new(0));
        let pend_flag_clone = pend_flag.clone();

        let consumer = thread::spawn(move || {
            while pend_flag_clone.load(Ordering::SeqCst) == 0 {
                scheduler::yield_me();
            }
            assert_eq!(mutex_consumer.nesting_count(), 1);

            let result = mutex_consumer.pend_for(5);
            assert!(!result);
            pend_flag_clone.fetch_add(1, Ordering::SeqCst);
        });
        mutex.pend_for(10);
        assert_eq!(mutex.nesting_count(), 1);
        pend_flag.fetch_add(1, Ordering::SeqCst);
        scheduler::yield_me();
        let start = time::get_sys_ticks();
        let mut current = time::get_sys_ticks();
        while current - start < 10 {
            scheduler::yield_me();
            current = time::get_sys_ticks();
        }
        mutex.post();
        while pend_flag.load(Ordering::SeqCst) != 2 {}
    }

    // Demonstrate a classic PI scene. Event orders,
    // t1[P3] acquires mu0.
    // t2[P6] acquires mu1
    // t2[P6] acquires mu0.
    // t0[P0] acquires mu1.
    #[test]
    fn test_blocking_mutex_chain_basic() {
        let clock = Arc::new(AtomicUsize::new(0));
        let mut mu = vec![Mutex::create(), Mutex::create(), Mutex::create()];
        let helper_mutex = Mutex::create();
        // t0.
        let t0 = {
            let mu = mu.clone();
            let clock_t0 = clock.clone();
            thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                let me = scheduler::current_thread();
                // crate::trace!("TH:0x{:x} t0 started", Thread::id(&me));
                // crate::trace!("t0 is waiting for 3");
                spin_until(3, &clock_t0);
                // t0 is ready to pend.
                // crate::trace!(
                //     "[TH:0x{:x}] t0 is ready to pend.",
                //     scheduler::current_thread_id()
                // );
                let ok = mu[1].pend_for(WAITING_FOREVER);
                assert!(ok);
                mu[1].post();
                clock_t0.fetch_add(1, Ordering::Relaxed);
            })))
            .set_priority(0 as ThreadPriority)
            .start()
        };
        // t1.
        {
            let mu = mu.clone();
            let clock = clock.clone();
            let helper_mutex = helper_mutex.clone();
            thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                let me = scheduler::current_thread();
                // crate::trace!("TH:0x{:x} t1 started", Thread::id(&me));
                // crate::trace!("t1 is waiting for 1");
                spin_until(1, &clock);
                let ok = mu[0].pend_for(WAITING_FOREVER);
                assert!(ok);
                assert_eq!(me.priority(), me.origin_priority());
                // Make t2 progress.
                // crate::trace!("Making t2 progress");
                clock.store(2, Ordering::Relaxed);
                // Waiting for t0 to promote my priority.
                let ok = helper_mutex.pend_for(WAITING_FOREVER);
                assert!(ok);
                // crate::trace!(
                //     "[TH:0x{:x}] t1 got the helper mutex",
                //     scheduler::current_thread_id()
                // );
                assert_eq!(me.priority(), 0);
                helper_mutex.post();
                mu[0].post();
                assert_eq!(me.priority(), me.origin_priority());
                clock.fetch_add(1, Ordering::Relaxed);
            })))
            .set_priority(3 as ThreadPriority)
            .start();
        }
        // t2.
        let t2 = {
            let mu = mu.clone();
            let clock = clock.clone();
            thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                let me = scheduler::current_thread();
                // crate::trace!("TH:0x{:x} t2 started", Thread::id(&me));
                // Waiting for t1".
                // crate::trace!("Waiting for t1");
                spin_until(2, &clock);
                // t1 make me progress.
                // crate::trace!("t1 make me progress.");
                let ok = mu[1].pend_for(WAITING_FOREVER);
                assert!(ok);
                // Acquired mu[1].
                assert_eq!(me.priority(), me.origin_priority());
                // t1 has acquired mu0.
                let ok = mu[0].pend_for(WAITING_FOREVER);
                assert!(ok);
                // t0 has made t1 progress.
                assert_eq!(me.priority(), 0);
                mu[0].post();
                mu[1].post();
                assert_eq!(me.priority(), me.origin_priority());
                clock.fetch_add(1, Ordering::Relaxed);
            })))
            .set_priority(6 as ThreadPriority)
            .start()
        };
        // Helper thread to inspect t0's state via spin.
        {
            let mu = mu.clone();
            let clock = clock.clone();
            let helper_mutex = helper_mutex.clone();
            let helper = thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                let me = scheduler::current_thread();
                // crate::trace!("TH:0x{:x} helper", Thread::id(&me));
                // crate::trace!("helper thread is running");
                let ok = helper_mutex.pend_for(WAITING_FOREVER);
                assert!(ok);
                // crate::trace!("helper thread acquired helper_mutex");
                clock.store(1, Ordering::Relaxed);
                // crate::trace!("t0 has suspended");
                loop {
                    if let Some(m) = t2.pending_on_mutex() {
                        if Arc::is(&m, &mu[0]) {
                            break;
                        }
                    };
                    // crate::trace!("Waiting t0 to be suspended");
                    scheduler::yield_me();
                    core::hint::spin_loop();
                }
                // crate::trace!("t2 has suspended on mu0");
                clock.store(3, Ordering::Relaxed);
                // crate::trace!("Make t1 progress");
                while t0.pending_on_mutex().is_none() {
                    // crate::trace!("Waiting t0 to be suspended");
                    scheduler::yield_me();
                    core::hint::spin_loop();
                }
                helper_mutex.post();
            })))
            .set_priority(0 as ThreadPriority)
            .start();
        }
        spin_until(6, &clock);
    }

    #[test]
    fn test_acquire_many_mutexes() {
        use crate::config::MAX_THREAD_PRIORITY;
        #[cfg(target_pointer_width = "32")]
        const N: usize = 64;
        #[cfg(target_pointer_width = "32")]
        const M: usize = N / 8;
        #[cfg(target_pointer_width = "64")]
        // FIXME: We still have performance issue under SMP mode. If number of
        // mutexes >= 64, it takes nearly one minute to finish.
        const N: usize = 256;
        #[cfg(target_pointer_width = "64")]
        const M: usize = N / 8;
        let counter = Arc::new(AtomicUsize::new(0));
        let mut mu = Arc::new(alloc::vec::Vec::new());
        for i in 0..M {
            unsafe { Arc::get_mut_unchecked(&mut mu) }.push(Mutex::create());
        }

        for i in 0..N {
            let prio = i % ((MAX_THREAD_PRIORITY + 1) as usize);
            let mu = mu.clone();
            let counter = counter.clone();
            let t = thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                for m in mu.iter() {
                    m.pend_for(WAITING_FOREVER);
                }
                for m in mu.iter().rev() {
                    m.post();
                }
                counter.fetch_add(1, Ordering::Relaxed);
                let this_thread = scheduler::current_thread();
                assert_eq!(this_thread.origin_priority(), this_thread.priority());
            })))
            .set_priority(MAX_THREAD_PRIORITY - (prio as ThreadPriority))
            .start();
        }
        spin_until(N, &counter);
    }

    type MutexGroup = Vec<Arc<Mutex>>;

    #[inline]
    fn create_mutex_group(n: usize) -> Arc<MutexGroup> {
        let mut mg = Arc::new(Vec::new());
        for i in 0..n {
            unsafe { Arc::get_mut_unchecked(&mut mg) }.push(Mutex::create());
        }
        mg
    }

    #[inline]
    fn pend_mutex_group(mg: &Arc<MutexGroup>) {
        for m in mg.iter() {
            m.pend_for(WAITING_FOREVER);
        }
    }

    #[inline]
    fn post_mutex_group(mg: &Arc<MutexGroup>) {
        for m in mg.iter().rev() {
            m.post()
        }
    }

    #[inline]
    fn pend_then_post_forked_mutex_groups(
        fst: &Arc<MutexGroup>,
        sec: &Arc<MutexGroup>,
        third: &Arc<MutexGroup>,
    ) {
        pend_mutex_group(fst);
        pend_mutex_group(sec);
        pend_mutex_group(third);
        post_mutex_group(third);
        post_mutex_group(sec);
        post_mutex_group(fst);
    }

    #[test]
    fn test_acquire_many_mutexes_1() {
        // This test aims to demonstrate our implementation doesn't make system
        // hang in a relatively complex scene.
        // Acquirement of mutex group shapes as follows
        // MG0   MG1
        // |_____|
        //    |
        //    MG2
        // ___|___
        // |     |
        // MG3   MG4
        // Thread group0 acquires MG0, MG2, MG3
        // Thread group1 acquires MG1, MG2, MG4
        use crate::config::MAX_THREAD_PRIORITY;
        #[cfg(target_pointer_width = "32")]
        const N: usize = 16;
        #[cfg(target_pointer_width = "32")]
        const M: usize = N / 4;
        #[cfg(target_pointer_width = "64")]
        // FIXME: We still have performance issue under SMP mode. If number of
        // mutexes >= 64, it takes nearly one minute to finish.
        const N: usize = 32;
        #[cfg(target_pointer_width = "64")]
        const M: usize = N / 4;
        let counter = Arc::new(AtomicUsize::new(0));
        let mg0 = create_mutex_group(M);
        let mg1 = create_mutex_group(M);
        let mg2 = create_mutex_group(M);
        let mg3 = create_mutex_group(M);
        let mg4 = create_mutex_group(M);
        // Create thread group0.
        for i in 0..N {
            let mg0 = mg0.clone();
            let mg2 = mg2.clone();
            let mg3 = mg3.clone();
            let counter = counter.clone();
            let prio = i % ((MAX_THREAD_PRIORITY + 1) as usize);
            thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                pend_then_post_forked_mutex_groups(&mg0, &mg2, &mg3);
                counter.fetch_add(1, Ordering::Relaxed);
                let this_thread = scheduler::current_thread();
                assert_eq!(this_thread.origin_priority(), this_thread.priority());
            })))
            .set_priority(MAX_THREAD_PRIORITY - (prio as ThreadPriority))
            .start();
        }
        // Create thread group1.
        for i in 0..N {
            let mg1 = mg0.clone();
            let mg2 = mg2.clone();
            let mg4 = mg3.clone();
            let counter = counter.clone();
            let prio = i % ((MAX_THREAD_PRIORITY + 1) as usize);
            thread::Builder::new(thread::Entry::Closure(Box::new(move || {
                pend_then_post_forked_mutex_groups(&mg1, &mg2, &mg4);
                counter.fetch_add(1, Ordering::Relaxed);
                let this_thread = scheduler::current_thread();
                assert_eq!(this_thread.origin_priority(), this_thread.priority());
            })))
            .set_priority(MAX_THREAD_PRIORITY - (prio as ThreadPriority))
            .start();
        }
        spin_until(2 * N, &counter);
    }
}
