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
    boards, config, scheduler, sync, thread,
    time::get_sys_ticks,
    types::{impl_simple_intrusive_adapter, Arc, ArcList, AtomicIlistHead as IlistHead},
};
use alloc::boxed::Box;
use bitflags::bitflags;
use core::{
    cmp, fmt,
    mem::MaybeUninit,
    sync::atomic::{AtomicU32, Ordering},
};
use log::warn;
use sync::spinlock::SpinLock;
use thread::{Entry, SystemThreadStorage, Thread, ThreadKind, ThreadNode};

const TIMER_WHEEL_SIZE: u32 = 32;

static HARD_TIMER_WHEEL: TimerWheel = TimerWheel::const_new();
#[cfg(soft_timer)]
static SOFT_TIMER_WHEEL: TimerWheel = TimerWheel::const_new();
#[cfg(soft_timer)]
static mut SOFT_TIMER_THREAD: MaybeUninit<ThreadNode> = MaybeUninit::zeroed();
#[cfg(soft_timer)]
static mut SOFT_TIMER_THREAD_STACK: SystemThreadStorage =
    SystemThreadStorage::const_new(ThreadKind::SoftTimer);

#[cfg(soft_timer)]
extern "C" fn run_soft_timer() {
    loop {
        let next_timeout = SOFT_TIMER_WHEEL.next_timeout();
        if next_timeout != usize::MAX {
            let ct = get_sys_ticks();
            let wait_time = next_timeout.saturating_sub(ct);
            if wait_time > 0 {
                scheduler::suspend_me_for(wait_time);
                let wakeup_ct = get_sys_ticks();
                if wakeup_ct < next_timeout {
                    continue;
                }
            }
            SOFT_TIMER_WHEEL.check_timer(next_timeout);
        } else {
            scheduler::suspend_me_for(super::WAITING_FOREVER);
        }
    }
}

pub fn system_timer_init() {
    HARD_TIMER_WHEEL.init();
    #[cfg(soft_timer)]
    {
        SOFT_TIMER_WHEEL.init();
        let th = thread::build_static_thread(
            unsafe { &mut SOFT_TIMER_THREAD },
            unsafe { &mut SOFT_TIMER_THREAD_STACK },
            config::SOFT_TIMER_THREAD_PRIORITY,
            thread::CREATED,
            Entry::C(run_soft_timer),
            ThreadKind::SoftTimer,
        );
        let ok = scheduler::queue_ready_thread(thread::CREATED, th);
        debug_assert!(ok);
    }
}

fn wakeup_soft_timer_thread() {
    let th = unsafe { SOFT_TIMER_THREAD.assume_init_ref() };
    if let Some(timer) = &th.timer {
        timer.stop();
    }
    let ok = scheduler::queue_ready_thread(thread::SUSPENDED, th.clone());
    debug_assert!(ok);
}

struct TimerWheel {
    wheel: SpinLock<[WheelTimerList; TIMER_WHEEL_SIZE as usize]>,
}

unsafe impl Sync for TimerWheel {}

impl TimerWheel {
    const fn const_new() -> Self {
        Self {
            wheel: SpinLock::const_new(
                [const { WheelTimerList::const_new() }; TIMER_WHEEL_SIZE as usize],
            ),
        }
    }

    fn init(&self) {
        let mut wheel = self.wheel.irqsave_lock();
        for i in 0..wheel.len() {
            let ok = wheel[i].init();
            debug_assert!(ok);
        }
    }

    fn add_timer(&self, mut timer: Arc<Timer>, timeout_ticks: usize) {
        let mut wheel = self.wheel.irqsave_lock();
        let cursor = timeout_ticks & (TIMER_WHEEL_SIZE as usize - 1);
        let it = wheel[cursor].iter();
        for mut t in it {
            if t.timeout_ticks() > timeout_ticks {
                WheelTimerList::insert_before(
                    unsafe { WheelTimerList::list_head_of_mut_unchecked(&mut t) },
                    timer,
                );
                return;
            }
        }
        wheel[cursor].push_back(timer.clone());
        #[cfg(soft_timer)]
        {
            if timer.is_soft() {
                wakeup_soft_timer_thread();
            }
        }
    }

    fn remove_timer(&self, timer: &mut Arc<Timer>) {
        let lock = self.wheel.irqsave_lock();
        WheelTimerList::detach(timer);
        drop(lock);
        #[cfg(soft_timer)]
        {
            if timer.is_soft() {
                wakeup_soft_timer_thread();
            }
        }
    }

    fn next_timeout(&self) -> usize {
        let mut next_timeout_tick = usize::MAX;
        let wheel = self.wheel.irqsave_lock();
        for i in 0..TIMER_WHEEL_SIZE as usize {
            if let Some(timer) = wheel[i].front() {
                let timeout_ticks = timer.timeout_ticks();
                if timeout_ticks < next_timeout_tick {
                    next_timeout_tick = timeout_ticks;
                }
            }
        }
        next_timeout_tick
    }

    fn check_timer(&self, current_ticks: usize) -> bool {
        let mut need_reschedule = false;
        let cursor = current_ticks & (TIMER_WHEEL_SIZE as usize - 1);
        let mut task_list = WheelTimerList::new();
        task_list.init();
        {
            let wheel = self.wheel.irqsave_lock();
            let mut iter = wheel[cursor].iter();
            for mut timer in iter {
                if timer.timeout_ticks() > current_ticks {
                    break;
                }
                WheelTimerList::detach(&mut timer);
                task_list.push_back(timer);
            }
        }

        while let Some(timer) = task_list.pop_front() {
            timer.run();
            need_reschedule = true;
            if timer.is_periodic() {
                timer.start();
            }
        }
        need_reschedule
    }
}

bitflags! {
    #[derive(Debug)]
    struct TimerFlags: u32 {
        const SOFT_TIMER = 1 << 0;
        const PERIODIC = 1 << 1;
        const ACTIVATED = 1 << 2;
    }
}

impl_simple_intrusive_adapter!(OffsetOfWheelNode, Timer, wheel_node);
type WheelTimerList = ArcList<Timer, OffsetOfWheelNode>;

#[derive(Debug)]
pub struct Timer {
    pub wheel_node: IlistHead<Timer, OffsetOfWheelNode>, // lock by TimerWheel
    flags: AtomicU32,
    inner: SpinLock<Inner>,
}

struct Inner {
    interval: usize,
    timeout_ticks: usize,
    callback: Option<Box<dyn Fn() + Send + Sync>>,
}

impl fmt::Debug for Inner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "interval: {}, timeout_ticks: {}",
            self.interval, self.timeout_ticks
        )
    }
}

impl Timer {
    #[cfg(soft_timer)]
    pub fn new_soft_oneshot(interval: usize, callback: Box<dyn Fn() + Send + Sync>) -> Arc<Self> {
        Self::new(interval, TimerFlags::SOFT_TIMER, callback)
    }

    #[cfg(soft_timer)]
    pub fn new_soft_periodic(interval: usize, callback: Box<dyn Fn() + Send + Sync>) -> Arc<Self> {
        Self::new(
            interval,
            TimerFlags::SOFT_TIMER | TimerFlags::PERIODIC,
            callback,
        )
    }

    pub fn new_hard_oneshot(interval: usize, callback: Box<dyn Fn() + Send + Sync>) -> Arc<Self> {
        Self::new(interval, TimerFlags::empty(), callback)
    }

    pub fn new_hard_periodic(interval: usize, callback: Box<dyn Fn() + Send + Sync>) -> Arc<Self> {
        Self::new(interval, TimerFlags::PERIODIC, callback)
    }

    fn new(interval: usize, flags: TimerFlags, callback: Box<dyn Fn() + Send + Sync>) -> Arc<Self> {
        Arc::new(Self {
            wheel_node: IlistHead::new(),
            flags: AtomicU32::new(flags.bits()),
            inner: SpinLock::new(Inner {
                interval,
                timeout_ticks: 0,
                callback: Some(callback),
            }),
        })
    }

    pub fn timeout_ticks(&self) -> usize {
        self.inner.irqsave_lock().timeout_ticks
    }

    pub fn is_soft(&self) -> bool {
        self.flags.load(Ordering::Relaxed) & TimerFlags::SOFT_TIMER.bits() != 0
    }

    pub fn is_periodic(&self) -> bool {
        self.flags.load(Ordering::Relaxed) & TimerFlags::PERIODIC.bits() != 0
    }

    pub fn is_activated(&self) -> bool {
        self.flags.load(Ordering::Relaxed) & TimerFlags::ACTIVATED.bits() != 0
    }

    pub fn set_callback(&self, callback: Box<dyn Fn() + Send + Sync>) {
        self.inner.irqsave_lock().callback = Some(callback);
    }

    pub fn start(&self) {
        #[cfg(soft_timer)]
        let is_soft = self.is_soft();

        if self.is_activated() {
            self.flags
                .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            // make_arc_from will increment the strong count of the Arc being cloned.
            let mut timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
            #[cfg(soft_timer)]
            if is_soft {
                SOFT_TIMER_WHEEL.remove_timer(&mut timer);
            } else {
                HARD_TIMER_WHEEL.remove_timer(&mut timer);
            }

            #[cfg(not(soft_timer))]
            {
                HARD_TIMER_WHEEL.remove_timer(&timer);
            }
        }

        let mut inner = self.inner.irqsave_lock();
        if inner.callback.is_none() {
            warn!("timer callback is None");
            return;
        }
        if inner.interval == 0 {
            // just run the callback and return
            inner.callback.take().unwrap()();
            return;
        }
        inner.timeout_ticks = get_sys_ticks().saturating_add(inner.interval);
        self.flags
            .fetch_or(TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);

        // make_arc_from will increment the strong count of the Arc being cloned.
        let timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
        #[cfg(soft_timer)]
        if is_soft {
            SOFT_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        } else {
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }

        #[cfg(not(soft_timer))]
        {
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }
    }

    pub fn start_new_interval(&self, interval: usize) {
        #[cfg(soft_timer)]
        let is_soft = self.is_soft();

        if self.is_activated() {
            self.flags
                .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            // make_arc_from will increment the strong count of the Arc being cloned.
            let mut timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
            #[cfg(soft_timer)]
            if is_soft {
                SOFT_TIMER_WHEEL.remove_timer(&mut timer);
            } else {
                HARD_TIMER_WHEEL.remove_timer(&mut timer);
            }

            #[cfg(not(soft_timer))]
            {
                HARD_TIMER_WHEEL.remove_timer(&timer);
            }
        }

        let mut inner = self.inner.irqsave_lock();
        inner.interval = interval;
        inner.timeout_ticks = get_sys_ticks().saturating_add(interval);
        self.flags
            .fetch_or(TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);

        // make_arc_from will increment the strong count of the Arc being cloned.
        let timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
        #[cfg(soft_timer)]
        if is_soft {
            SOFT_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        } else {
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }

        #[cfg(not(soft_timer))]
        {
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }
    }

    pub fn stop(&self) {
        if self.is_activated() {
            self.flags
                .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);

            #[cfg(soft_timer)]
            let is_soft = self.is_soft();

            // remove from wheel first
            let mut timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
            #[cfg(soft_timer)]
            if is_soft {
                SOFT_TIMER_WHEEL.remove_timer(&mut timer);
            } else {
                HARD_TIMER_WHEEL.remove_timer(&mut timer);
            }

            #[cfg(not(soft_timer))]
            {
                HARD_TIMER_WHEEL.remove_timer(&timer);
            }
        }
    }

    pub fn reset(&self) {
        #[cfg(soft_timer)]
        let is_soft = self.is_soft();

        let mut timer = unsafe { WheelTimerList::make_arc_from(&self.wheel_node) };
        #[cfg(soft_timer)]
        if is_soft {
            if self.is_activated() {
                self.flags
                    .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
                SOFT_TIMER_WHEEL.remove_timer(&mut timer);
            }
            let mut inner = self.inner.irqsave_lock();
            inner.timeout_ticks = get_sys_ticks().saturating_add(inner.interval);
            self.flags
                .fetch_or(TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            SOFT_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        } else {
            if self.is_activated() {
                self.flags
                    .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
                HARD_TIMER_WHEEL.remove_timer(&mut timer);
            }
            let mut inner = self.inner.irqsave_lock();
            inner.timeout_ticks = get_sys_ticks().saturating_add(inner.interval);
            self.flags
                .fetch_or(TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }

        #[cfg(not(soft_timer))]
        {
            if self.is_activated() {
                self.flags
                    .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
                HARD_TIMER_WHEEL.remove_timer(&timer);
            }
            let mut inner = self.inner.irqsave_lock();
            inner.timeout_ticks = get_sys_ticks().saturating_add(inner.interval);
            self.flags
                .fetch_or(TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            HARD_TIMER_WHEEL.add_timer(timer, inner.timeout_ticks);
        }
    }

    // this function can only used in check_timer and tests
    pub fn run(&self) {
        if self.is_activated() {
            self.flags
                .fetch_and(!TimerFlags::ACTIVATED.bits(), Ordering::Relaxed);
            let mut inner = self.inner.irqsave_lock();
            if let Some(callback) = inner.callback.take() {
                callback();
                if self.is_periodic() {
                    inner.callback = Some(callback);
                }
            }
        }
    }
}

// used for systick
pub(crate) fn check_hard_timer(tick: usize) -> bool {
    HARD_TIMER_WHEEL.check_timer(tick)
}
// used for tickless
pub(crate) fn get_next_timer_ticks() -> usize {
    #[cfg(soft_timer)]
    {
        cmp::min(
            SOFT_TIMER_WHEEL.next_timeout(),
            HARD_TIMER_WHEEL.next_timeout(),
        )
    }
    #[cfg(not(soft_timer))]
    {
        HARD_TIMER_WHEEL.next_timeout()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Arc;
    use alloc::vec::Vec;
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};

    // Helper function to create a simple callback
    fn create_test_callback(counter: Arc<AtomicUsize>) -> Box<dyn Fn() + Send + Sync + 'static> {
        Box::new(move || {
            counter.fetch_add(1, Ordering::Relaxed);
        })
    }

    #[test]
    fn test_timer_creation() {
        #[cfg(soft_timer)]
        {
            let counter = Arc::new(AtomicUsize::new(0));
            let callback = create_test_callback(counter.clone());

            let soft_oneshot = Timer::new_soft_oneshot(10, callback);
            assert!(!soft_oneshot.is_activated());
            assert!(!soft_oneshot.is_periodic());

            let counter2 = Arc::new(AtomicUsize::new(0));
            let callback2 = create_test_callback(counter2.clone());

            // Test soft periodic timer
            let soft_periodic = Timer::new_soft_periodic(10, callback2);
            assert!(!soft_periodic.is_activated());
            assert!(soft_periodic.is_periodic());

            scheduler::suspend_me_for(10);
            assert_eq!(counter.load(Ordering::Relaxed), 0);
            assert_eq!(counter2.load(Ordering::Relaxed), 0);
        }

        let counter3 = Arc::new(AtomicUsize::new(0));
        let callback3 = create_test_callback(counter3.clone());

        // Test hard one-shot timer
        let hard_oneshot = Timer::new_hard_oneshot(10, callback3);
        assert!(!hard_oneshot.is_activated());
        assert!(!hard_oneshot.is_periodic());

        let counter4 = Arc::new(AtomicUsize::new(0));
        let callback4 = create_test_callback(counter4.clone());

        // Test hard periodic timer
        let hard_periodic = Timer::new_hard_periodic(10, callback4);
        assert!(!hard_periodic.is_activated());
        assert!(hard_periodic.is_periodic());

        // timer will never run
        scheduler::suspend_me_for(10);
        assert_eq!(counter3.load(Ordering::Relaxed), 0);
        assert_eq!(counter4.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_timer_start_stop() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        // Test start
        timer.start();
        assert!(timer.is_activated());
        let timeout_ticks = timer.timeout_ticks();
        assert!(timeout_ticks > 0); // Should have a valid timeout

        // Test stop
        timer.stop();
        assert!(!timer.is_activated());

        // Test start again
        timer.start();
        assert!(timer.is_activated());

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_reset() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        let original_timeout = timer.timeout_ticks();

        scheduler::suspend_me_for(1);

        // Reset timer
        timer.reset();
        let new_timeout = timer.timeout_ticks();
        assert!(new_timeout > original_timeout); // Should be later

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_start_new_interval() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        let original_timeout = timer.timeout_ticks();

        // Change interval
        timer.start_new_interval(20);
        let new_timeout = timer.timeout_ticks();
        assert!(new_timeout > original_timeout); // Should be later due to longer interval

        scheduler::suspend_me_for(20);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_run_callback() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        // Timer not activated, callback should not run
        timer.run();
        assert_eq!(counter.load(Ordering::Relaxed), 0);

        // Activate timer and run callback
        timer.start();
        timer.run();
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_wheel_operations() {
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        let callback1 = create_test_callback(counter1.clone());
        let callback2 = create_test_callback(counter2.clone());

        let timer1 = Timer::new_hard_oneshot(10, callback1);
        let timer2 = Timer::new_hard_oneshot(20, callback2);

        // Start both timers
        timer1.start();
        timer2.start();

        let timeout1 = timer1.timeout_ticks();
        let timeout2 = timer2.timeout_ticks();
        assert!(timeout1 < timeout2); // First timer should expire earlier

        // Check next timeout
        let next_timeout = get_next_timer_ticks();
        assert!(next_timeout <= timeout1); // Should be the earlier timer

        scheduler::suspend_me_for(10);
        assert_eq!(counter1.load(Ordering::Relaxed), 1);

        scheduler::suspend_me_for(10);
        assert_eq!(counter2.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_periodic_timer() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_periodic(10, callback);

        timer.start();
        let first_timeout = timer.timeout_ticks();

        // Simulate timer expiration by calling run directly
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
        assert!(timer.is_activated()); // Should still be active for periodic timer

        // Check that timeout was updated
        let second_timeout = timer.timeout_ticks();
        assert!(second_timeout > first_timeout); // Should be rescheduled

        timer.stop();
    }

    #[test]
    fn test_multiple_timers_same_timeout() {
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        let counter3 = Arc::new(AtomicUsize::new(0));

        let callback1 = create_test_callback(counter1.clone());
        let callback2 = create_test_callback(counter2.clone());
        let callback3 = create_test_callback(counter3.clone());

        let timer1 = Timer::new_hard_oneshot(10, callback1);
        let timer2 = Timer::new_hard_oneshot(10, callback2);
        let timer3 = Timer::new_hard_oneshot(10, callback3);

        // Start all timers with same timeout
        timer1.start();
        timer2.start();
        timer3.start();

        scheduler::suspend_me_for(10);

        // All timers should have fired
        assert_eq!(counter1.load(Ordering::Relaxed), 1);
        assert_eq!(counter2.load(Ordering::Relaxed), 1);
        assert_eq!(counter3.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_stop_while_active() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        assert!(timer.is_activated());

        // Stop timer before it expires
        timer.stop();
        assert!(!timer.is_activated());

        // Timer will not run
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_timer_restart_while_active() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        let first_timeout = timer.timeout_ticks();

        scheduler::suspend_me_for(5);

        // Restart timer before it expires
        timer.start();
        let second_timeout = timer.timeout_ticks();
        assert!(second_timeout > first_timeout); // Should be later

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_edge_cases() {
        // Test with zero interval
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(0, callback);

        timer.start();
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_ordering() {
        // Test that timers are properly ordered by timeout
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        let counter3 = Arc::new(AtomicUsize::new(0));

        let callback1 = create_test_callback(counter1.clone());
        let callback2 = create_test_callback(counter2.clone());
        let callback3 = create_test_callback(counter3.clone());

        let timer1 = Timer::new_hard_oneshot(30, callback1);
        let timer2 = Timer::new_hard_oneshot(10, callback2);
        let timer3 = Timer::new_hard_oneshot(20, callback3);

        // Start timers in different order
        timer1.start(); // longest timeout
        timer3.start(); // medium timeout
        timer2.start(); // shortest timeout

        let timeout1 = timer1.timeout_ticks();
        let timeout2 = timer2.timeout_ticks();
        let timeout3 = timer3.timeout_ticks();

        // Check ordering
        assert!(timeout2 < timeout3);
        assert!(timeout3 < timeout1);

        scheduler::suspend_me_for(30);
        assert_eq!(counter1.load(Ordering::Relaxed), 1);
        assert_eq!(counter2.load(Ordering::Relaxed), 1);
        assert_eq!(counter3.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_flags() {
        let counter = Arc::new(AtomicUsize::new(0));

        // Test soft timer
        #[cfg(soft_timer)]
        {
            let callback = create_test_callback(counter.clone());
            let soft_timer = Timer::new_soft_oneshot(10, callback);
            assert!(!soft_timer.is_periodic());
        }

        let callback = create_test_callback(counter.clone());
        // Test hard timer
        let hard_timer = Timer::new_hard_oneshot(10, callback);
        assert!(!hard_timer.is_periodic());

        let callback = create_test_callback(counter.clone());
        // Test periodic timer
        let periodic_timer = Timer::new_hard_periodic(10, callback);
        assert!(periodic_timer.is_periodic());
    }

    #[test]
    fn test_timer_concurrent_access() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Arc::new(Timer::new_hard_oneshot(10, callback));

        // Simulate concurrent access by cloning Arc
        let timer_clone1 = timer.clone();
        let timer_clone2 = timer.clone();

        // Start from one clone
        timer_clone1.start();
        assert!(timer_clone1.is_activated());
        assert!(timer_clone2.is_activated()); // Should be the same timer

        // Stop from another clone
        timer_clone2.stop();
        assert!(!timer_clone1.is_activated());
        assert!(!timer_clone2.is_activated());

        // timer should not run
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_timer_wheel_capacity() {
        // Test timer wheel with many timers
        let mut timers = Vec::new();
        let mut counters = Vec::new();

        // Create many timers
        for i in 0..20 {
            let counter = Arc::new(AtomicUsize::new(0));
            let callback = create_test_callback(counter.clone());
            let timer = Timer::new_hard_oneshot(10 + i, callback);

            timer.start();
            assert!(timer.is_activated());
            timers.push(timer);
            counters.push(counter);
        }
        scheduler::suspend_me_for(10);

        // Check all timers fired
        for counter in &counters {
            assert_eq!(counter.load(Ordering::Relaxed), 1);
            scheduler::suspend_me_for(1);
        }
    }

    #[test]
    fn test_timer_oneshot_behavior() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        assert!(timer.is_activated());

        // Run timer once
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        // For oneshot timer, it should not be reactivated automatically
        // The timer should remain inactive after running
        assert!(!timer.is_activated());
    }

    #[test]
    fn test_timer_periodic_reactivation() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_periodic(10, callback);

        timer.start();
        assert!(timer.is_activated());

        // Run timer multiple times
        for i in 0..5 {
            scheduler::suspend_me_for(10);
            assert_eq!(counter.load(Ordering::Relaxed), i + 1);
            assert!(timer.is_activated()); // Should remain active
        }
        timer.stop();
    }

    #[test]
    fn test_timer_timeout_accuracy() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(100, callback);

        timer.start();
        let timeout = timer.timeout_ticks();

        // The timeout should be current time + interval
        // Since we can't mock get_sys_ticks easily, we just verify it's reasonable
        assert!(timeout > 0);
        assert!(timeout >= 100); // Should be at least the interval

        timer.stop();
    }

    #[test]
    fn test_timer_state_transitions() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        // Initial state
        assert!(!timer.is_activated());

        // Start -> Active
        timer.start();
        assert!(timer.is_activated());

        // Stop -> Inactive
        timer.stop();
        assert!(!timer.is_activated());

        // Start again -> Active
        timer.start();
        assert!(timer.is_activated());

        scheduler::suspend_me_for(1);

        // Reset while active -> Still active with new timeout
        let old_timeout = timer.timeout_ticks();
        timer.reset();
        let new_timeout = timer.timeout_ticks();
        assert!(timer.is_activated());
        assert!(new_timeout > old_timeout);

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_wheel_overflow() {
        // Test timer wheel behavior with overflow scenarios
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());

        // Create timer with large interval that might cause overflow
        let timer = Timer::new_hard_oneshot(usize::MAX - 100, callback);
        timer.start();

        // Should handle overflow gracefully
        let timeout = timer.timeout_ticks();
        assert!(timeout > 0);
        timer.stop();
    }

    #[cfg(soft_timer)]
    #[test]
    fn test_timer_soft_vs_hard() {
        // Test differences between soft and hard timers
        let counter1 = Arc::new(AtomicUsize::new(0));
        let counter2 = Arc::new(AtomicUsize::new(0));
        let callback1 = create_test_callback(counter1.clone());
        let callback2 = create_test_callback(counter2.clone());

        let soft_timer = Timer::new_soft_oneshot(10, callback1);
        let hard_timer = Timer::new_hard_oneshot(10, callback2);

        // Both should behave similarly for basic operations
        soft_timer.start();
        hard_timer.start();

        assert!(soft_timer.is_activated());
        assert!(hard_timer.is_activated());

        scheduler::suspend_me_for(11);

        assert_eq!(counter1.load(Ordering::Relaxed), 1);
        assert_eq!(counter2.load(Ordering::Relaxed), 1);
        assert_eq!(SOFT_TIMER_WHEEL.next_timeout(), usize::MAX);
    }

    #[test]
    fn test_timer_interval_changes() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_periodic(10, callback);

        timer.start();
        let original_timeout = timer.timeout_ticks();

        // Change interval while running
        timer.start_new_interval(20);
        let new_timeout = timer.timeout_ticks();
        assert!(new_timeout - original_timeout >= 10); // Should be later due to longer interval

        // Run timer and check it uses new interval
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 0);

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        timer.stop();
    }

    #[test]
    fn test_timer_cleanup_after_stop() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        assert!(timer.is_activated());

        // Stop timer
        timer.stop();
        assert!(!timer.is_activated());

        // Try to run stopped timer
        timer.run();
        assert_eq!(counter.load(Ordering::Relaxed), 0); // Should not execute

        // Restart timer
        timer.start();
        assert!(timer.is_activated());
        timer.run();
        assert_eq!(counter.load(Ordering::Relaxed), 1); // Should execute now
                                                        // will inactive after run
        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_multiple_starts() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        // Multiple starts should be handled gracefully
        timer.start();
        let timeout1 = timer.timeout_ticks();

        timer.start();
        let timeout2 = timer.timeout_ticks();

        timer.start();
        let timeout3 = timer.timeout_ticks();

        // All should be valid timeouts
        assert!(timeout1 > 0);
        assert!(timeout2 > 0);
        assert!(timeout3 > 0);

        // Timer should remain active
        assert!(timer.is_activated());

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_timer_wheel_removal() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Timer::new_hard_oneshot(10, callback);

        timer.start();
        assert!(timer.is_activated());

        // Stop timer (removes from wheel)
        timer.stop();
        assert!(!timer.is_activated());
    }

    #[test]
    fn test_timer_concurrent_modification() {
        let counter = Arc::new(AtomicUsize::new(0));
        let callback = create_test_callback(counter.clone());
        let timer = Arc::new(Timer::new_hard_periodic(10, callback));

        let timer1 = timer.clone();
        let timer2 = timer.clone();

        // Concurrent start and stop operations
        timer1.start();
        assert!(timer1.is_activated());

        timer2.stop();
        assert!(!timer1.is_activated());
        assert!(!timer2.is_activated());

        // Restart and test concurrent run
        timer1.start();

        scheduler::suspend_me_for(10);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        timer1.stop();
    }
}
