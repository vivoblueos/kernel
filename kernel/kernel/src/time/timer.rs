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

// FIXME: The shared timer queue and expiration barrier make one hart's timer
// interrupt depend on another hart's callback duration. Retrying on contention
// prevents a lost local clock, but per-CPU timer queues are the better fix.
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

#[cfg(timer_align)]
pub const ALIGN_INSENSITIVE: u8 = 1 << 1;
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
    // Flag bits (`ALIGN_INSENSITIVE`). Bit 0 is reserved for a future
    // LOW_POWER port so the two lineages can share the layout.
    flags: u8,
}

impl Timer {
    pub const fn new() -> Self {
        Self {
            node: TimerNode::new(),
            mode: TimerMode::Deadline(Tick(0)),
            callback: TimerCallback::Nothing,
            expired: AtomicBool::new(false),
            flags: 0,
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

    #[cfg(timer_align)]
    #[inline]
    pub fn set_align_insensitive(&mut self) {
        self.flags |= ALIGN_INSENSITIVE;
    }

    #[cfg(timer_align)]
    #[inline]
    pub fn is_align_insensitive(&self) -> bool {
        self.flags & ALIGN_INSENSITIVE != 0
    }

    #[cfg(not(timer_align))]
    #[inline]
    pub fn is_align_insensitive(&self) -> bool {
        false
    }
}

/// Alignment policy: rewrites a timer's deadline onto an anchor's phase grid.
pub trait AlignPolicy {
    /// Called under irqsave guard before `add`. `heap` supplies anchor candidates.
    fn maybe_align(
        &self,
        tm: &mut Timer,
        now: Tick,
        heap: &IntrusiveBinaryHeap<Timer, Node, Comparator>,
    );
}

/// Disabled no-op: inlined away.
pub struct AlignDisabled;

impl AlignPolicy for AlignDisabled {
    #[inline(always)]
    fn maybe_align(
        &self,
        _tm: &mut Timer,
        _now: Tick,
        _heap: &IntrusiveBinaryHeap<Timer, Node, Comparator>,
    ) {
    }
}

/// Enabled: scans anchors and rewrites base_deadline via `decide_align`.
#[cfg(timer_align)]
pub struct AlignEnabled;

#[cfg(timer_align)]
impl AlignPolicy for AlignEnabled {
    fn maybe_align(
        &self,
        tm: &mut Timer,
        now: Tick,
        heap: &IntrusiveBinaryHeap<Timer, Node, Comparator>,
    ) {
        use crate::time::timer_align::{decide_align, AlignedStart};
        if !tm.is_align_insensitive() {
            return;
        }
        let TimerMode::Repeat(r) = &mut tm.mode else {
            return;
        };
        if r.period.0 == 0 {
            return;
        }
        let new_period = r.period;
        let new_original = r.base_deadline;
        let tol = blueos_kconfig::CONFIG_TIMER_ALIGN_TOLERANCE_TICKS as usize;
        let anchors = heap.iter().filter_map(|t| match &t.mode {
            TimerMode::Repeat(ar) if t.is_align_insensitive() && ar.period.0 != 0 => {
                Some((ar.base_deadline, ar.period))
            }
            _ => None,
        });
        if let Some(AlignedStart { deadline }) =
            decide_align(new_period, new_original, now, tol, anchors)
        {
            r.base_deadline = deadline;
        }
    }
}

/// cfg-dispatched entry point so call sites need no scattered `#[cfg]`.
pub struct AlignActive;

impl AlignActive {
    #[inline(always)]
    pub fn maybe_align(
        &self,
        tm: &mut Timer,
        now: Tick,
        heap: &IntrusiveBinaryHeap<Timer, Node, Comparator>,
    ) {
        #[cfg(timer_align)]
        {
            AlignEnabled.maybe_align(tm, now, heap)
        }
        #[cfg(not(timer_align))]
        {
            AlignDisabled.maybe_align(tm, now, heap)
        }
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
        AlignActive.maybe_align(tm, Tick::now(), w.timers());
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
    let res;
    {
        let mut w = HW_TIMERS.irqsave_lock();
        res = w.add(tm);
    }
    update_clock_interrupt();
    res
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

pub(crate) enum ExpireTimersResult {
    NextDeadline(Tick),
    Idle,
    BarrierBusy,
}

pub(crate) fn expire_timers(deadline: Tick) -> ExpireTimersResult {
    let Some(_guard) = EXPIRE_BARRIER.try_irqsave_lock() else {
        return ExpireTimersResult::BarrierBusy;
    };

    let soft_deadline = wake_up_soft_timer_worker(deadline).unwrap_or(Tick::MAX);
    let hard_deadline;
    let res;
    {
        let mut w = HW_TIMERS.irqsave_lock();
        let _expired_count = w.expire(deadline);
        w.post_expire();
        hard_deadline = w.next_deadline().unwrap_or(Tick::MAX);
        res = core::cmp::min(soft_deadline, hard_deadline);
    }
    if res == Tick::MAX {
        return ExpireTimersResult::Idle;
    }
    ExpireTimersResult::NextDeadline(res)
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

    #[cfg(timer_align)]
    #[test]
    fn align_insensitive_flag_roundtrip() {
        let mut tm = Timer::new();
        assert!(!tm.is_align_insensitive());
        tm.set_align_insensitive();
        assert!(tm.is_align_insensitive());
    }

    #[cfg(not(timer_align))]
    #[test]
    fn align_insensitive_always_false_when_disabled() {
        let tm = Timer::new();
        assert!(!tm.is_align_insensitive());
    }

    #[cfg(timer_align)]
    #[test]
    fn align_disabled_is_noop() {
        let mut tm = Timer::new();
        tm.mode = TimerMode::Repeat(Repeat {
            base_deadline: Tick(42),
            period: Tick(10),
            total_times: None,
            elapsed_times: 0,
        });
        let original = Tick(42);
        // Empty heap: AlignDisabled is a no-op.
        let empty: IntrusiveBinaryHeap<Timer, Node, Comparator> =
            IntrusiveBinaryHeap::<Timer, Node, _>::new(compare_timer);
        AlignDisabled.maybe_align(&mut tm, Tick(0), &empty);
        match tm.mode {
            TimerMode::Repeat(r) => assert_eq!(r.base_deadline, original),
            _ => debug_assert!(false, "expected Repeat mode"),
        }
    }

    #[cfg(timer_align)]
    #[test]
    fn align_enabled_aligns_to_anchor() {
        // Anchor period 10 base 0; new period 10 base 29, now 25, tol 1 -> snaps to 30.
        let mut anchor = Timer::new();
        anchor.mode = TimerMode::Repeat(Repeat {
            base_deadline: Tick(0),
            period: Tick(10),
            total_times: None,
            elapsed_times: 0,
        });
        anchor.set_align_insensitive();
        let mut heap: IntrusiveBinaryHeap<Timer, Node, Comparator> =
            IntrusiveBinaryHeap::<Timer, Node, _>::new(compare_timer);
        heap.push(&mut anchor);
        let mut tm = Timer::new();
        tm.mode = TimerMode::Repeat(Repeat {
            base_deadline: Tick(29),
            period: Tick(10),
            total_times: None,
            elapsed_times: 0,
        });
        tm.set_align_insensitive();
        AlignEnabled.maybe_align(&mut tm, Tick(25), &heap);
        match tm.mode {
            TimerMode::Repeat(r) => assert_eq!(r.base_deadline, Tick(30)),
            _ => debug_assert!(false, "expected Repeat mode"),
        }
    }

    #[cfg(timer_align)]
    #[test]
    fn base_deadline_snap_locks_phase_permanently() {
        // B-specific: snapping base_deadline once locks ALL future
        // base + period*elapsed on the grid (A's rolling model cannot do this).
        // Anchor p=10 base=0; new p=10 base=9, now=5, tol=1 -> |10-9|=1<=1 -> snaps to 10.
        let mut anchor = Timer::new();
        anchor.mode = TimerMode::Repeat(Repeat {
            base_deadline: Tick(0),
            period: Tick(10),
            total_times: None,
            elapsed_times: 0,
        });
        anchor.set_align_insensitive();
        let mut heap: IntrusiveBinaryHeap<Timer, Node, Comparator> =
            IntrusiveBinaryHeap::<Timer, Node, _>::new(compare_timer);
        heap.push(&mut anchor);
        let mut tm = Timer::new();
        tm.mode = TimerMode::Repeat(Repeat {
            base_deadline: Tick(9),
            period: Tick(10),
            total_times: None,
            elapsed_times: 0,
        });
        tm.set_align_insensitive();
        AlignEnabled.maybe_align(&mut tm, Tick(5), &heap);
        match &tm.mode {
            TimerMode::Repeat(r) => {
                assert_eq!(r.base_deadline, Tick(10));
                // Every future deadline stays on-grid at multiples of 10.
                for elapsed in 0..5usize {
                    let next = compute_next_deadline_with(&tm, elapsed);
                    assert_eq!(
                        next.0 % 10,
                        0,
                        "elapsed={} deadline={} not on grid",
                        elapsed,
                        next.0
                    );
                }
            }
            _ => debug_assert!(false, "expected Repeat mode"),
        }
    }

    /// Helper: compute deadline as if the timer had the given elapsed_times.
    fn compute_next_deadline_with(tm: &Timer, elapsed: usize) -> Tick {
        match &tm.mode {
            TimerMode::Repeat(r) => Tick(r.base_deadline.0 + r.period.0 * elapsed),
            TimerMode::Deadline(d) => *d,
        }
    }

    #[test]
    fn timer_size_invariant_across_cfg() {
        // Timer is #[repr(C)]; the align flag must not change its layout.
        let s = core::mem::size_of::<Timer>();
        assert!(s > 0);
    }

    #[test]
    fn test_oneshot_hwtm() {
        let counter = Arc::new(AtomicUsize::new(0));
        let deadline = Tick::after(Tick(10));
        with_iou!(|iou| {
            let mut timer = Timer::new();
            timer.mode = TimerMode::Deadline(deadline);
            timer.callback = create_test_callback(&counter);
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
        let deadline = Tick::after(Tick(10));
        with_iou!(|iou| {
            let mut swtm = Timer::new();
            swtm.mode = TimerMode::Deadline(deadline);
            swtm.callback = callback;
            iou = add_soft_timer(&mut swtm).unwrap();
            // Wait for the soft timer to execute by polling the counter.
            // This avoids race conditions from tick drift on QEMU RISC-V.
            while counter.load(Ordering::Relaxed) == 0 {
                scheduler::yield_me();
            }
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
        with_iou!(|iou| {
            let mut tm = Timer::new();
            tm.mode = TimerMode::Repeat(r);
            tm.callback = callback;
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
        with_iou!(|iou| {
            let mut tm = Timer::new();
            tm.mode = TimerMode::Repeat(r);
            tm.callback = callback;
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

        with_iou!(|iou1, iou2, iou3| {
            let mut timer1 = Timer::new();
            timer1.mode = TimerMode::Deadline(deadline);
            timer1.callback = callback1;
            let mut timer2 = Timer::new();
            timer2.mode = TimerMode::Deadline(deadline);
            timer2.callback = callback2;
            let mut timer3 = Timer::new();
            timer3.mode = TimerMode::Deadline(deadline);
            timer3.callback = callback3;
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

    // FIXME: On SMP, another CPU may hold EXPIRE_BARRIER, causing the clock
    // interrupt to skip expiration and defer it until a later timer interrupt.
    // This test can remove the timer before that interrupt executes its callback.
    // There is no good solution with the shared timer queues yet; revisit this
    // test when per-CPU timers are available.
    #[cfg(not(smp))]
    #[test]
    fn test_timer_edge_cases() {
        // Test with zero interval.
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(&counter);
        assert!(arch::local_irq_enabled());
        with_iou!(|iou| {
            let mut timer = Timer::new();
            timer.mode = TimerMode::Deadline(Tick(0));
            timer.callback = callback;
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
        let deadline = Tick::after(Tick(8));
        with_iou!(|iou| {
            let mut timer = Timer::new();
            timer.mode = TimerMode::Deadline(deadline);
            timer.callback = callback;
            iou = add_hard_timer(&mut timer).unwrap();
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
        let mut deadline = Tick::after(Tick(13));
        with_iou!(|iou| {
            let mut timer = Timer::new();
            timer.mode = TimerMode::Repeat(Repeat {
                base_deadline: deadline,
                period: Tick(7),
                total_times: None,
                elapsed_times: 0,
            });
            timer.callback = callback;
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
        // FIXME: Allow wider tolerance for QEMU virtualized environments where timer
        // precision can be affected by host system load and CPU scheduling.
        assert!((10..=20).contains(&diff), "diff = {}, expected 10", diff);
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
        use crate::boards::ClockImpl;
        use blueos_hal::clock::Clock;
        let start = ClockImpl::estimate_current_cycles();
        scheduler::suspend_me_for::<()>(
            Tick(blueos_kconfig::CONFIG_TICKS_PER_SECOND as usize),
            None,
        );
        let end = crate::boards::ClockImpl::estimate_current_cycles();
        let diff = end - start;
        // Accept interval [0.99, 1.10].
        let hz = ClockImpl::hz();
        let l = 99;
        // FIXME: Allow wider tolerance for QEMU virtualized environments where timer
        // precision can be affected by host system load and CPU scheduling.
        let r = 1_10;
        assert!(
            diff >= l * hz / 1_00,
            "Timer fired too early: diff = {}, expected at least {}",
            diff,
            l * hz / 1_00
        );
        assert!(
            diff <= r * hz / 1_00,
            "Timer fired too late: diff = {}, expected at most {}",
            diff,
            r * hz / 1_00
        );
    }

    #[cfg(all(soft_timer, timer_align))]
    #[test]
    fn align_010_same_period_coalesce() {
        // Two same-period (10) insensitive timers: b's first fire is 2 ticks off
        // the anchor phase (<= TOL=2 -> snaps). Coalescing check: both fire on the
        // same tick (diff == 0).
        //
        // B uses the arithmetic model: first fire = base_deadline (+ period*0).
        // So a.base = now+10 (fires now+10); b.base = now+12, snaps to nearest grid
        // point now+10 (|12-10|=2 <= TOL), fires now+10 -> coalesces with a.
        let ticks: Arc<SpinLock<Vec<Tick>>> = Arc::new(SpinLock::new(Vec::new()));
        let now = Tick::now();
        with_iou!(|iou_a, iou_b| {
            let mut a = Timer::new();
            a.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(10)),
                period: Tick(10),
                total_times: Some(1),
                elapsed_times: 0,
            });
            a.set_align_insensitive();
            a.callback = {
                let ticks = ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_a = add_soft_timer(&mut a).unwrap();

            let mut b = Timer::new();
            // b's original first fire is 2 ticks off the anchor phase (<= TOL=2 -> snaps).
            b.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(12)),
                period: Tick(10),
                total_times: Some(1),
                elapsed_times: 0,
            });
            b.set_align_insensitive();
            b.callback = {
                let ticks = ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_b = add_soft_timer(&mut b).unwrap();

            scheduler::suspend_me_until::<()>(now.add(Tick(15)), None);
            iou_a = remove_soft_timer(iou_a).unwrap();
            iou_b = remove_soft_timer(iou_b).unwrap();
        });
        let recorded = ticks.irqsave_lock();
        assert_eq!(recorded.len(), 2, "both timers should fire once each");
        assert_eq!(
            recorded[0],
            recorded[1],
            "coalesced: both fire on same tick, got {:?}",
            recorded.clone()
        );
    }

    #[cfg(all(soft_timer, timer_align))]
    #[test]
    fn align_016_non_integer_no_align() {
        // 13 vs 8 is not an integer multiple -> no alignment, each fires independently
        // (no-align check: fire ticks differ, diff != 0).
        //
        // B arithmetic model: a.base = now+13 (fires now+13); b.base = now+8 (fires now+8).
        // 13%8 != 0 and 8%13 != 0 -> decide_align returns None -> b keeps its base.
        let ticks: Arc<SpinLock<Vec<Tick>>> = Arc::new(SpinLock::new(Vec::new()));
        let now = Tick::now();
        with_iou!(|iou_a, iou_b| {
            let mut a = Timer::new();
            a.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(13)),
                period: Tick(13),
                total_times: Some(1),
                elapsed_times: 0,
            });
            a.set_align_insensitive();
            a.callback = {
                let ticks = ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_a = add_soft_timer(&mut a).unwrap();

            let mut b = Timer::new();
            b.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(8)),
                period: Tick(8),
                total_times: Some(1),
                elapsed_times: 0,
            });
            b.set_align_insensitive();
            b.callback = {
                let ticks = ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_b = add_soft_timer(&mut b).unwrap();

            scheduler::suspend_me_until::<()>(now.add(Tick(20)), None);
            iou_a = remove_soft_timer(iou_a).unwrap();
            iou_b = remove_soft_timer(iou_b).unwrap();
        });
        let recorded = ticks.irqsave_lock();
        assert_eq!(recorded.len(), 2, "both timers should fire once each");
        assert_ne!(
            recorded[0],
            recorded[1],
            "non-integer-multiple must NOT coalesce, got same tick {:?}",
            recorded.clone()
        );
    }

    #[cfg(all(soft_timer, timer_align))]
    #[test]
    fn align_020_integer_multiple_aligns() {
        // Integer-multiple alignment: anchor a period 20, newcomer b period 40 (x2).
        // B's arithmetic model: first fire = base_deadline, and snapping base_deadline
        // once locks ALL future base + period*elapsed on the grid.
        //
        // a: base=now+20, period=20, total=2 -> fires now+20, now+40.
        // b: base=now+42 (2 off grid point now+40, <= TOL=2 -> snaps to now+40),
        //    period=40, total=1 -> fires now+40, same tick as a's 2nd fire.
        // Unaligned, b would fire at now+42 (offset%20==2), failing the assert below.
        let a_ticks: Arc<SpinLock<Vec<Tick>>> = Arc::new(SpinLock::new(Vec::new()));
        let b_ticks: Arc<SpinLock<Vec<Tick>>> = Arc::new(SpinLock::new(Vec::new()));
        let now = Tick::now();
        with_iou!(|iou_a, iou_b| {
            let mut a = Timer::new();
            a.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(20)),
                period: Tick(20),
                total_times: Some(2),
                elapsed_times: 0,
            });
            a.set_align_insensitive();
            a.callback = {
                let ticks = a_ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_a = add_soft_timer(&mut a).unwrap();

            let mut b = Timer::new();
            // b's original first fire is 2 ticks off grid point now+40 -> <= TOL=2 snaps.
            b.mode = TimerMode::Repeat(Repeat {
                base_deadline: now.add(Tick(42)),
                period: Tick(40),
                total_times: Some(1),
                elapsed_times: 0,
            });
            b.set_align_insensitive();
            b.callback = {
                let ticks = b_ticks.clone();
                TimerCallback::Do(Box::new(move || {
                    ticks.irqsave_lock().push(Tick::now());
                }))
            };
            iou_b = add_soft_timer(&mut b).unwrap();

            // Window covers now+40 (a's 2nd fire and b's 1st fire on the same tick).
            scheduler::suspend_me_until::<()>(now.add(Tick(45)), None);
            iou_a = remove_soft_timer(iou_a).unwrap();
            iou_b = remove_soft_timer(iou_b).unwrap();
        });

        let b_recorded = b_ticks.irqsave_lock();
        assert_eq!(
            b_recorded.len(),
            1,
            "b should fire once, got {:?}",
            b_recorded.clone()
        );
        let b_fire = b_recorded[0];
        let a_recorded = a_ticks.irqsave_lock();
        assert_eq!(
            a_recorded.len(),
            2,
            "a should fire twice, got {:?}",
            a_recorded.clone()
        );

        // Integer-multiple alignment core assertion: b's fire tick lands on anchor a's grid.
        let offset = b_fire.0.saturating_sub(now.0);
        assert_eq!(
            offset % 20,
            0,
            "integer-multiple: b must fire on anchor grid (offset%20==0), \
             b_fire={:?} now={:?} offset={} a_fires={:?}",
            b_fire,
            now,
            offset,
            a_recorded.clone()
        );
        // b's fire tick equals a's 2nd fire tick (drain on the same tick).
        assert_eq!(
            b_fire,
            a_recorded[1],
            "b should coalesce onto a's second fire, got b={:?} a={:?}",
            b_fire,
            a_recorded.clone()
        );
    }
}
