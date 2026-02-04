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

use crate::{
    arch,
    boards::ClockImpl,
    config::MAX_THREAD_PRIORITY,
    scheduler, static_arc,
    sync::{atomic_wait, atomic_wake, SpinLock},
    thread,
    thread::{Entry, SystemThreadStorage, ThreadKind, ThreadNode},
    time::{
        timer_manager::{Iou, TimerManager},
        Tick,
    },
    types::{
        impl_simple_intrusive_adapter, IntrusiveAdapter, IntrusiveBinaryHeap,
        IntrusiveBinaryHeapNode, IouIntrusiveBinaryHeapNodeMut,
    },
};
use alloc::boxed::Box;
use core::{
    mem::MaybeUninit,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};

static_arc! {
    HW_TIMERS(SpinLock<TimerManager>, SpinLock::new(TimerManager::new())),
}
#[cfg(soft_timer)]
static mut SW_TIMER_WORKER: SoftTimerWorker = SoftTimerWorker::new();

static EXPIRE_BARRIER: SpinLock<()> = SpinLock::new(());

struct SoftTimerWorker {
    waker: AtomicUsize,
    timers: SpinLock<TimerManager>,
    storage: SystemThreadStorage,
    thread: MaybeUninit<ThreadNode>,
}

impl SoftTimerWorker {
    pub const fn new() -> Self {
        Self {
            waker: AtomicUsize::new(0),
            timers: SpinLock::new(TimerManager::new()),
            storage: SystemThreadStorage::new(ThreadKind::SoftTimer),
            thread: MaybeUninit::zeroed(),
        }
    }
}

extern "C" fn run_soft_timer() {
    loop {
        let n = unsafe { &SW_TIMER_WORKER.waker }.load(Ordering::Relaxed);
        {
            let mut w = unsafe { &SW_TIMER_WORKER.timers }.irqsave_lock();
            w.post_expire();
        }
        update_clock_interrupt();
        atomic_wait(unsafe { &SW_TIMER_WORKER.waker }, n, Tick::MAX);
    }
}

// Wake up worker to run bottom half.
fn wake_up_soft_timer_worker(deadline: Tick) -> Option<Tick> {
    let res;
    {
        let mut w = unsafe { &SW_TIMER_WORKER.timers }.irqsave_lock();
        w.expire(deadline);
        res = w.next_deadline();
    }
    unsafe { &SW_TIMER_WORKER.waker }.fetch_add(1, Ordering::Relaxed);
    atomic_wake(unsafe { &SW_TIMER_WORKER.waker }, 1);
    res
}

pub(crate) fn init() {
    #[cfg(soft_timer)]
    {
        let worker = thread::build_static_thread(
            unsafe { &mut SW_TIMER_WORKER.thread },
            unsafe { &mut SW_TIMER_WORKER.storage },
            0,
            thread::IDLE,
            Entry::C(run_soft_timer),
            ThreadKind::SoftTimer,
        );
        let ok = scheduler::queue_ready_thread(thread::IDLE, worker);
        debug_assert_eq!(ok, Ok(()));
    }
}

#[derive(Debug, Default)]
pub struct Repeat {
    pub base_deadline: Tick,
    pub period: Tick,
    pub total_times: Option<usize>,
    pub elapsed_times: usize,
}

#[derive(Debug)]
pub enum TimerMode {
    Deadline(Tick),
    Repeat(Repeat),
}

pub enum TimerCallback {
    Nothing,
    Resched(Option<ThreadNode>, bool),
    Do(Box<dyn Fn()>),
    Posix(
        extern "C" fn(arg: *mut core::ffi::c_void),
        *mut core::ffi::c_void,
    ),
    UnsafePosix(
        unsafe extern "C" fn(arg: *mut core::ffi::c_void),
        *mut core::ffi::c_void,
    ),
}

impl core::fmt::Debug for TimerCallback {
    fn fmt(&self, _: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        Ok(())
    }
}

#[derive(Default, Debug)]
pub struct Node;
impl const IntrusiveAdapter<Timer> for Node {
    fn offset() -> usize {
        core::mem::offset_of!(Timer, node)
    }
}

// To support concurrent modification of inner data of the timer, we have
// to refactor it to something like
// ```
// struct Timer {
//     node: IntrusiveBinaryHeapNode<Timer, Node>,
//     control: Arc<Mutex<TimerControl>>,
// }
// ```
// At the moment, we don't need concurrent modification yet.
#[derive(Debug)]
#[repr(C)]
pub struct Timer {
    // FIXME: If we need to check if the Timer is active, we should call
    // IntrusiveBinaryHeap::is_active.
    node: IntrusiveBinaryHeapNode<Timer, Node>,
    pub mode: TimerMode,
    pub callback: TimerCallback,
    // Support concurrent expiring via atomic.
    expired: AtomicBool,
}

impl Timer {
    pub const fn new() -> Self {
        Self {
            node: TimerNode::new(),
            mode: TimerMode::Deadline(Tick(0)),
            callback: TimerCallback::Nothing,
            expired: AtomicBool::new(false),
        }
    }

    pub fn expire(&self) {
        self.expired.store(true, Ordering::Relaxed);
    }

    pub fn expired(&self) -> bool {
        self.expired.load(Ordering::Relaxed)
    }

    pub unsafe fn reset(&self) {
        self.expired.store(false, Ordering::SeqCst);
    }
}

pub type TimerNode = IntrusiveBinaryHeapNode<Timer, Node>;

pub(crate) type Comparator = fn(&Timer, &Timer) -> core::cmp::Ordering;

pub(crate) fn compute_next_deadline(tm: &Timer) -> Tick {
    match &tm.mode {
        TimerMode::Deadline(d) => *d,
        TimerMode::Repeat(r) => Tick(r.base_deadline.0 + r.period.0 * r.elapsed_times),
    }
}

pub(crate) fn compare_timer(lhs: &Timer, rhs: &Timer) -> core::cmp::Ordering {
    let lhs = compute_next_deadline(lhs);
    let rhs = compute_next_deadline(rhs);
    lhs.0.cmp(&rhs.0)
}

pub fn add_soft_timer(tm: &mut Timer) -> Option<Iou<'_>> {
    let mut iou;
    {
        let swtm = unsafe { &SW_TIMER_WORKER.timers };
        let mut w = swtm.irqsave_lock();
        iou = w.add(tm);
    }
    update_clock_interrupt();
    iou
}

pub fn remove_soft_timer<'a>(iou: Iou<'_>) -> Option<Iou<'a>> {
    let res;
    {
        let swtm = unsafe { &SW_TIMER_WORKER.timers };
        let mut w = swtm.irqsave_lock();
        res = w.remove(iou);
    }
    update_clock_interrupt();
    res
}

pub fn add_hard_timer(tm: &mut Timer) -> Option<Iou<'_>> {
    let mut iou;
    {
        let mut w = HW_TIMERS.irqsave_lock();
        iou = w.add(tm);
    }
    update_clock_interrupt();
    iou
}

pub fn remove_hard_timer<'a>(iou: Iou<'_>) -> Option<Iou<'a>> {
    let res;
    {
        let mut w = HW_TIMERS.irqsave_lock();
        res = w.remove(iou);
    }
    update_clock_interrupt();
    res
}

pub fn is_active_hard_timer(iou: &Iou<'_>) -> bool {
    let mut w = HW_TIMERS.irqsave_lock();
    w.is_active(iou)
}

pub fn is_active_soft_timer(iou: &Iou<'_>) -> bool {
    let mut w = unsafe { &SW_TIMER_WORKER.timers }.irqsave_lock();
    w.is_active(iou)
}

pub(crate) fn expire_timers(deadline: Tick) -> Option<Tick> {
    let _guard = EXPIRE_BARRIER.try_irqsave_lock()?;
    let soft_deadline = wake_up_soft_timer_worker(deadline).unwrap_or(Tick::MAX);
    let soft_deadline = Tick::MAX;
    let hard_deadline;
    let res;
    {
        let mut w = HW_TIMERS.irqsave_lock();
        w.expire(deadline);
        w.post_expire();
        hard_deadline = w.next_deadline().unwrap_or(Tick::MAX);
        res = core::cmp::min(soft_deadline, hard_deadline);
    }
    if res == Tick::MAX {
        return None;
    }
    Some(res)
}

fn update_clock_interrupt() -> Tick {
    let soft_deadline = {
        let mut w = unsafe { &SW_TIMER_WORKER.timers }.irqsave_lock();
        w.next_deadline().unwrap_or(Tick::MAX)
    };
    let hard_deadline = HW_TIMERS
        .irqsave_lock()
        .next_deadline()
        .unwrap_or(Tick::MAX);
    let next_deadline = core::cmp::min(soft_deadline, hard_deadline);
    Tick::interrupt_at(next_deadline);
    next_deadline
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{sync::SpinLock, types::Arc, with_iou};
    use alloc::vec::Vec;
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};

    fn create_test_callback(counter: &Arc<AtomicUsize>) -> TimerCallback {
        let closure = {
            let counter = counter.clone();
            move || {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        };
        TimerCallback::Do(Box::new(closure))
    }

    #[test]
    fn test_oneshot_hwtm() {
        let counter = Arc::new(AtomicUsize::new(0));
        let deadline = Tick::after(Tick(10));
        let mut timer = Timer::new();
        timer.mode = TimerMode::Deadline(deadline);
        timer.callback = create_test_callback(&counter);
        with_iou!(|iou| {
            iou = add_hard_timer(&mut timer).unwrap();
            scheduler::suspend_me_until::<()>(deadline, None);
            iou = remove_hard_timer(iou).unwrap();
        });
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[cfg(soft_timer)]
    #[test]
    fn test_oneshot_swtm() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let mut swtm = Timer::new();
        let deadline = Tick::after(Tick(10));
        swtm.mode = TimerMode::Deadline(deadline);
        swtm.callback = callback;
        with_iou!(|iou| {
            iou = add_soft_timer(&mut swtm).unwrap();
            // The SW timer worker is working at priority 0, so should be as realtime
            // as the HW timer.
            scheduler::suspend_me_until::<()>(deadline.add(Tick(1)), None);
            iou = remove_soft_timer(iou).unwrap();
        });
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_periodic_hwtm() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let deadline = Tick::after(Tick(5));
        let r = Repeat {
            base_deadline: deadline,
            period: Tick(5),
            total_times: Some(5),
            elapsed_times: 0,
        };
        let mut tm = Timer::new();
        tm.mode = TimerMode::Repeat(r);
        tm.callback = callback;
        with_iou!(|iou| {
            iou = add_hard_timer(&mut tm).unwrap();
            scheduler::suspend_me_until::<()>(deadline.add(Tick(20)), None);
            iou = remove_hard_timer(iou).unwrap();
        });
        assert_eq!(counter.load(Ordering::Relaxed), 5);
    }

    #[cfg(soft_timer)]
    #[test]
    fn test_periodic_swtm() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let base_deadline = Tick::after(Tick(5));
        let r = Repeat {
            base_deadline,
            period: Tick(10),
            total_times: Some(3),
            elapsed_times: 0,
        };
        let mut tm = Timer::new();
        tm.mode = TimerMode::Repeat(r);
        tm.callback = callback;
        with_iou!(|iou| {
            iou = add_soft_timer(&mut tm).unwrap();
            scheduler::suspend_me_until::<()>(base_deadline.add(Tick(21)), None);
            iou = remove_soft_timer(iou).unwrap();
        });
        assert_eq!(counter.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn test_multiple_timers_same_timeout() {
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        let counter3 = Arc::new(AtomicUsize::new(0));

        let callback1 = create_test_callback(&counter1);
        let callback2 = create_test_callback(&counter2);
        let callback3 = create_test_callback(&counter3);
        let deadline = Tick::after(Tick(10));

        let mut timer1 = Timer::new();
        timer1.mode = TimerMode::Deadline(deadline);
        timer1.callback = callback1;
        let mut timer2 = Timer::new();
        timer2.mode = TimerMode::Deadline(deadline);
        timer2.callback = callback2;
        let mut timer3 = Timer::new();
        timer3.mode = TimerMode::Deadline(deadline);
        timer3.callback = callback3;

        with_iou!(|iou1, iou2, iou3| {
            iou1 = add_hard_timer(&mut timer1).unwrap();
            iou2 = add_hard_timer(&mut timer2).unwrap();
            iou3 = add_hard_timer(&mut timer3).unwrap();
            scheduler::suspend_me_until::<()>(deadline, None);
            iou1 = remove_hard_timer(iou1).unwrap();
            iou2 = remove_hard_timer(iou2).unwrap();
            iou3 = remove_hard_timer(iou3).unwrap();
        });
        // All timers should have fired.
        assert_eq!(counter1.load(Ordering::Relaxed), 1);
        assert_eq!(counter2.load(Ordering::Relaxed), 1);
        assert_eq!(counter3.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_edge_cases() {
        // Test with zero interval.
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let mut timer = Timer::new();
        timer.mode = TimerMode::Deadline(Tick(0));
        timer.callback = callback;
        assert!(arch::local_irq_enabled());
        with_iou!(|iou| {
            iou = add_hard_timer(&mut timer).unwrap();
            // Clock interrupt should be triggered here.
            iou = remove_hard_timer(iou).unwrap();
        });
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    fn create_callback_for_ordering(
        order: &Arc<SpinLock<Vec<Arc<Timer>>>>,
        tm: &Arc<Timer>,
    ) -> TimerCallback {
        let closure = {
            let order = order.clone();
            let tm = tm.clone();
            move || {
                order.irqsave_lock().push(tm.clone());
            }
        };
        TimerCallback::Do(Box::new(closure))
    }

    #[test]
    fn test_timer_ordering() {
        // Test that timers are properly ordered by timeout.
        let order = Arc::new(SpinLock::new(Vec::new()));

        let mut timer1 = Arc::new(Timer::new());
        {
            let cb = create_callback_for_ordering(&order, &timer1);
            let mut w = unsafe { Arc::get_mut_unchecked(&mut timer1) };
            w.mode = TimerMode::Deadline(Tick::after(Tick(30)));
            w.callback = cb;
        }

        let mut timer2 = Arc::new(Timer::new());
        {
            let cb = create_callback_for_ordering(&order, &timer2);
            let mut w = unsafe { Arc::get_mut_unchecked(&mut timer2) };
            w.mode = TimerMode::Deadline(Tick::after(Tick(10)));
            w.callback = cb;
        }

        let mut timer3 = Arc::new(Timer::new());
        {
            let cb = create_callback_for_ordering(&order, &timer3);
            let mut w = unsafe { Arc::get_mut_unchecked(&mut timer3) };
            w.mode = TimerMode::Deadline(Tick::after(Tick(20)));
            w.callback = cb;
        }

        with_iou!(|iou1, iou2, iou3| {
            iou1 = add_hard_timer(unsafe { Arc::get_mut_unchecked(&mut timer1) }).unwrap();
            iou2 = add_hard_timer(unsafe { Arc::get_mut_unchecked(&mut timer2) }).unwrap();
            iou3 = add_hard_timer(unsafe { Arc::get_mut_unchecked(&mut timer3) }).unwrap();
            scheduler::suspend_me_for::<()>(Tick(30), None);
            iou1 = remove_hard_timer(iou1).unwrap();
            iou2 = remove_hard_timer(iou2).unwrap();
            iou3 = remove_hard_timer(iou3).unwrap();
        });
        let mut r = order.irqsave_lock();
        assert_eq!(r.len(), 3);
        assert!(Arc::is(&r[0], &timer2));
        assert!(Arc::is(&r[1], &timer3));
        assert!(Arc::is(&r[2], &timer1));
    }

    #[test]
    fn test_timer_oneshot_behavior() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let mut timer = Timer::new();
        let mut deadline = Tick::after(Tick(8));
        timer.mode = TimerMode::Deadline(deadline);
        timer.callback = callback;
        with_iou!(|iou| {
            let iou = add_hard_timer(&mut timer).unwrap();
            assert!(is_active_hard_timer(&iou));
            scheduler::suspend_me_until::<()>(deadline, None);
            assert_eq!(counter.load(Ordering::Relaxed), 1);
            // For oneshot timer, it should not be reactivated automatically
            // The timer should remain inactive after running.
            assert!(!is_active_hard_timer(&iou));
            iou = remove_hard_timer(iou).unwrap();
        });
    }

    #[test]
    fn test_timer_periodic_reactivation() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        let mut timer = Timer::new();
        let mut deadline = Tick::after(Tick(13));
        timer.mode = TimerMode::Repeat(Repeat {
            base_deadline: deadline,
            period: Tick(7),
            total_times: None,
            elapsed_times: 0,
        });
        timer.callback = callback;
        with_iou!(|iou| {
            iou = add_hard_timer(&mut timer).unwrap();
            // Run timer multiple times.
            for i in 0..5 {
                assert!(is_active_hard_timer(&iou));
                assert_eq!(counter.load(Ordering::Relaxed), i);
                scheduler::suspend_me_until::<()>(deadline, None);
                deadline = deadline.add(Tick(7));
            }
            iou = remove_hard_timer(iou).unwrap();
        });
    }

    #[test]
    fn test_timer_timeout_accuracy() {
        let base = Tick::now();
        let deadline = base.add(Tick(10));
        scheduler::suspend_me_until::<()>(deadline, None);
        let now = Tick::now();
        let diff = now.0 - base.0;
        // Should be no diff for hard timer at low workload.
        assert_eq!(diff, 10);
    }

    #[cfg(soft_timer)]
    #[test]
    fn test_timer_soft_vs_hard() {
        // Test differences between soft and hard timers
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        with_iou!(|hwiou, swiou| {
            let mut deadline = Tick::after(Tick(8));
            let mut hwtm = Timer::new();
            hwtm.mode = TimerMode::Deadline(deadline);
            let callback1 = create_test_callback(&counter1);
            hwtm.callback = callback1;
            let mut swtm = Timer::new();
            swtm.mode = TimerMode::Deadline(deadline);
            let callback2 = create_test_callback(&counter2);
            swtm.callback = callback2;
            hwiou = add_hard_timer(&mut hwtm).unwrap();
            swiou = add_soft_timer(&mut swtm).unwrap();
            assert!(is_active_hard_timer(&hwiou));
            assert!(is_active_soft_timer(&swiou));
            scheduler::suspend_me_until::<()>(deadline, None);
            assert_eq!(counter1.load(Ordering::Relaxed), 1);
            scheduler::suspend_me_until::<()>(deadline.add(Tick(1)), None);
            assert_eq!(counter2.load(Ordering::Relaxed), 1);
            {
                let mut w = unsafe { &SW_TIMER_WORKER.timers }.irqsave_lock();
                let res = w.next_deadline();
                assert!(res.is_none());
            }
            hwiou = remove_hard_timer(hwiou).unwrap();
            swiou = remove_soft_timer(swiou).unwrap();
        });
    }

    #[test]
    fn test_timer_accuracy() {
        use crate::{boards::ClockImpl, devices::clock::Clock};
        let start = ClockImpl::estimate_current_cycles();
        scheduler::suspend_me_for::<()>(
            Tick(blueos_kconfig::CONFIG_TICKS_PER_SECOND as usize),
            None,
        );
        let end = crate::boards::ClockImpl::estimate_current_cycles();
        let diff = end - start;
        // Accept interval [0.99, 1.01].
        let hz = ClockImpl::hz();
        let l = 99;
        let r = 1_01;
        assert!(diff >= l * hz / 1_00);
        assert!(diff <= r * hz / 1_00);
    }
}
