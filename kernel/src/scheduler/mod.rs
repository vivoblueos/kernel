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
    arch, signal,
    support::DisableInterruptGuard,
    sync::SpinLockGuard,
    thread,
    thread::{Entry, GlobalQueueVisitor, Thread, ThreadNode},
    time,
    time::{
        timer,
        timer::{Timer, TimerCallback, TimerMode, TimerNode},
        timer_manager::Iou as TimerIou,
        Tick,
    },
    types::{Arc, IlistHead, Uint},
};
use alloc::boxed::Box;
use core::{
    intrinsics::unlikely,
    mem::MaybeUninit,
    sync::atomic::{compiler_fence, AtomicBool, AtomicU8, Ordering},
};
pub use global_scheduler::*;
pub(crate) use wait_queue::*;

mod global_scheduler;
mod idle;
pub use idle::{
    current_idle_thread, current_idle_thread_ref, get_idle_thread, get_idle_thread_ref,
};
pub(crate) mod wait_queue;

static READY_CORES: AtomicU8 = AtomicU8::new(0);
const NUM_CORES: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum InsertMode {
    /// Insert by priority
    InsertByPrio = 0,
    /// Append to end
    InsertToEnd = 1,
}

impl InsertMode {
    /// Convert InsertMode to u8 const
    pub const fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Const type for InsertByPrio
pub struct InsertByPrio;
impl InsertByPrio {
    pub const MODE: InsertMode = InsertMode::InsertByPrio;
    pub const VALUE: u8 = 0;
}

/// Const type for InsertToEnd  
pub struct InsertToEnd;
impl InsertToEnd {
    pub const MODE: InsertMode = InsertMode::InsertToEnd;
    pub const VALUE: u8 = 1;
}

/// Trait for InsertMode const types
pub trait InsertModeTrait {
    const MODE: InsertMode;
}

impl InsertModeTrait for InsertByPrio {
    const MODE: InsertMode = InsertMode::InsertByPrio;
}

impl InsertModeTrait for InsertToEnd {
    const MODE: InsertMode = InsertMode::InsertToEnd;
}

pub(crate) static mut RUNNING_THREADS: [MaybeUninit<ThreadNode>; NUM_CORES] =
    [const { MaybeUninit::zeroed() }; NUM_CORES];
static mut PER_CPU_TIMER: [MaybeUninit<Timer>; NUM_CORES] =
    [const { MaybeUninit::zeroed() }; NUM_CORES];

pub(crate) fn init() {
    idle::init_idle_threads();
    global_scheduler::init();
    init_timers();
}

fn init_timers() {
    for pct in unsafe { &mut PER_CPU_TIMER }.iter_mut().take(NUM_CORES) {
        let mut tm = Timer::new();
        pct.write(tm);
    }
}

fn set_per_cpu_timer(id: usize, deadline: Tick) {
    debug_assert_ne!(deadline, Tick::MAX);
    debug_assert!(!arch::local_irq_enabled());
    unsafe {
        let iou = TimerIou::from_mut(PER_CPU_TIMER[id].assume_init_mut());
        timer::remove_hard_timer(iou);
        let tm_mut = PER_CPU_TIMER[id].assume_init_mut();
        tm_mut.reset();
        let TimerMode::Deadline(d) = &mut tm_mut.mode else {
            panic!("PER_CPU_TIMER is in a wrong mode")
        };
        *d = deadline;
        let _ = timer::add_hard_timer(tm_mut).unwrap();
    }
}

fn set_current_timer(deadline: Tick) {
    set_per_cpu_timer(arch::current_cpu_id(), deadline);
}

pub(crate) struct ContextSwitchHookHolder {
    next_thread: *const Thread,
}

impl ContextSwitchHookHolder {
    pub fn new(next_thread: ThreadNode) -> Self {
        Self {
            next_thread: unsafe { Arc::into_raw(next_thread) },
        }
    }

    pub unsafe fn next_thread(&self) -> &Thread {
        &*self.next_thread
    }
}

fn prepare_signal_handling(t: &ThreadNode) {
    // Save the context being restored first.
    let mut l = t.lock();
    if !l.activate_signal_context() {
        return;
    };
    let ctx = l.saved_sp() as *mut arch::Context;
    let ctx = unsafe { &mut *ctx };
    // Update ctx so that signal context will be restored.
    ctx.set_return_address(arch::switch_stack as usize)
        .set_arg(0, l.signal_handler_sp())
        .set_arg(1, signal::handler_entry as usize);
}

#[inline]
pub(crate) fn spin_until_ready_to_run(t: &Thread) -> usize {
    let mut saved_sp;
    loop {
        saved_sp = t.saved_sp();
        if saved_sp != 0 {
            break;
        }
        core::hint::spin_loop();
    }
    saved_sp
}

// Must use next's thread's stack or system stack to exeucte this function.
// We assume this hook is invoked with local irq disabled.
pub(crate) extern "C" fn save_context_finish_hook(
    hook: &mut ContextSwitchHookHolder,
    old_sp: usize,
) -> usize {
    // We must be careful that the last use of the `hook` must happen-before
    // setting the prev thread's saved_sp since the `hook` is still on the stack
    // of the prev thread. To resolve race condition of the stack, we first take
    // the ownership of all pending actions in the `hook`, so that these actions
    // are on current stack.
    // FIXME: We must be careful about performance issue of Option::take, since besides
    // loading content from the Option, storing None into the Option also happens.
    let next = unsafe { Arc::from_raw(hook.next_thread) };
    switch_current_thread(next, old_sp)
}

fn switch_current_thread(next: ThreadNode, old_sp: usize) -> usize {
    let now = Tick::now();
    #[cfg(robin_scheduler)]
    {
        next.set_this_round_start_at(now);
        let time_slices = next.refresh_time_slices();
        let deadline = now.add(time_slices);
        set_current_timer(deadline);
    }
    #[cfg(thread_stats)]
    let cycles = time::current_clock_cycles();
    #[cfg(thread_stats)]
    next.lock().set_start_cycles(cycles);
    let next_id = Thread::id(&next);
    let next_priority = next.priority();
    let next_saved_sp = spin_until_ready_to_run(&next);
    // Handling signals relies on previously saved sp, so it must be put between
    // spin_until_ready_to_run and clear_saved_sp.
    // FIXME: Signal feature should be optional.
    {
        if next.lock().has_pending_signals() {
            prepare_signal_handling(&next);
        }
    }
    next.clear_saved_sp();
    let ok = next.transfer_state(thread::READY, thread::RUNNING);
    debug_assert_eq!(ok, Ok(()));
    let mut old = set_current_thread(next);
    #[cfg(thread_stats)]
    old.lock().increment_cycles(cycles);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "Switching from 0x{:x}: {{ SP: 0x{:x} PRI: {} }} to 0x{:x}: {{ SP: 0x{:x} PRI: {} }}",
        Thread::id(&old),
        old.saved_sp(),
        old.priority(),
        next_id,
        next_saved_sp,
        next_priority,
    );
    #[cfg(robin_scheduler)]
    {
        let start = old.this_round_start_at();
        let elapsed = now.since(start);
        old.elapse_time_slices(elapsed);
    }
    #[cfg(thread_stats)]
    old.lock().increment_cycles(cycles);
    if old.state() == thread::RETIRED {
        let cleanup = old.lock().take_cleanup();
        if let Some(entry) = cleanup {
            match entry {
                Entry::C(f) => f(),
                Entry::Closure(f) => f(),
                Entry::Posix(f, arg) => f(arg),
            }
        };
        GlobalQueueVisitor::remove(&mut old);
        if ThreadNode::strong_count(&old) != 1 {
            // TODO: Add warning log that there are still references to the old thread.
        }
    }
    old.set_saved_sp(old_sp);
    next_saved_sp
}

// It's usually used in cortex-m's pendsv handler.
pub(crate) extern "C" fn relinquish_me_and_return_next_sp(old_sp: usize) -> usize {
    debug_assert!(!arch::local_irq_enabled());
    debug_assert!(!crate::irq::is_in_irq());
    debug_assert_eq!(current_thread_ref().preempt_count(), 0);
    let Some(next) = next_preferred_thread(current_thread_ref().priority()) else {
        #[cfg(debugging_scheduler)]
        crate::trace!("[TH:0x{:x}] keeps running", current_thread_id());
        return old_sp;
    };
    debug_assert_eq!(next.state(), thread::READY);
    let old = current_thread_ref();
    if Thread::id(old) == Thread::id(idle::current_idle_thread_ref()) {
        let ok = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert_eq!(ok, Ok(()));
    } else {
        let ok = queue_ready_thread(thread::RUNNING, unsafe { Arc::clone_from(old) });
        debug_assert_eq!(ok, Ok(()));
    };

    switch_current_thread(next, old_sp)
}

pub fn retire_me() -> ! {
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
    debug_assert_eq!(next.state(), thread::READY);
    #[cfg(procfs)]
    {
        let _ = crate::vfs::trace_thread_close(current_thread());
    }
    // FIXME: Some WaitQueue might still share the ownership of
    // the `old`, shall we record which WaitQueue the `old`
    // belongs to? Weak reference might not help to reduce memory
    // usage.
    let mut hooks = ContextSwitchHookHolder::new(next);
    let ok = current_thread_ref().transfer_state(thread::RUNNING, thread::RETIRED);
    debug_assert_eq!(ok, Ok(()));
    arch::switch_context_with_hook(&mut hooks as *mut _);
    unreachable!("Retired thread should not reach here")
}

fn inner_yield(next: ThreadNode) {
    let old = current_thread();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    old.disable_preempt();
    if Thread::id(&old) == Thread::id(idle::current_idle_thread_ref()) {
        let ok = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert_eq!(ok, Ok(()));
    } else {
        let ok = queue_ready_thread(thread::RUNNING, old.clone());
        debug_assert_eq!(ok, Ok(()));
    };
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
}

pub fn yield_me() {
    // We don't allow thread yielding with irq disabled.
    // The scheduler assumes every thread should be resumed with local
    // irq enabled.
    debug_assert!(arch::local_irq_enabled());
    let Some(next) = next_ready_thread() else {
        return;
    };
    debug_assert_eq!(next.state(), thread::READY);
    inner_yield(next);
}

pub fn relinquish_me() {
    debug_assert!(arch::local_irq_enabled());
    let old = current_thread_ref();
    let Some(next) = next_preferred_thread(old.priority()) else {
        return;
    };
    debug_assert_eq!(next.state(), thread::READY);
    inner_yield(next);
}

pub fn suspend_me_for<T>(mut timeout: Tick, wq: Option<SpinLockGuard<'_, T>>) -> bool {
    if timeout != Tick::MAX {
        timeout = Tick::after(timeout);
    }
    suspend_me_until(timeout, wq)
}

pub fn suspend_me_until<T>(deadline: Tick, wq: Option<SpinLockGuard<'_, T>>) -> bool {
    if unlikely(!is_schedule_ready()) {
        return false;
    }
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] is looking for the next thread",
        current_thread_id()
    );
    let old = current_thread_ref();
    let current_idle = idle::current_idle_thread_ref();
    debug_assert_ne!(Thread::id(old), Thread::id(current_idle));
    let next = next_ready_thread().map_or_else(|| unsafe { Arc::clone_from(current_idle) }, |v| v);
    debug_assert_eq!(next.state(), thread::READY);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] next thread is 0x{:x}",
        current_thread_id(),
        Thread::id(&next)
    );
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    old.disable_preempt();
    let ok = old.transfer_state(thread::RUNNING, thread::SUSPENDED);
    debug_assert_eq!(ok, Ok(()));
    drop(wq);
    let mut reached_deadline = false;
    if deadline != Tick::MAX {
        let mut tm = Timer::new();
        tm.mode = TimerMode::Deadline(deadline);
        tm.callback = TimerCallback::Resched(Some(unsafe { Arc::clone_from(old) }), false);
        let mut iou;
        {
            iou = timer::add_hard_timer(&mut tm).unwrap();
            arch::switch_context_with_hook(&mut hook_holder as *mut _);
            iou = timer::remove_hard_timer(iou).unwrap();
            reached_deadline = match tm.callback {
                TimerCallback::Resched(_, timeout) => timeout,
                _ => false,
            };
        }
        drop(iou);
    } else {
        arch::switch_context_with_hook(&mut hook_holder as *mut _);
    }
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
    reached_deadline
}

// Yield me immediately if not in ISR, otherwise switch context on
// exiting of the inner most ISR. Or just do nothing if underling arch
// doesn't have good support of this semantics. Cortex-m's pendsv is
// perfectly meet this semantics.
pub fn yield_me_now_or_later() {
    if unlikely(!is_schedule_ready()) {
        return;
    }
    if current_thread_ref().preempt_count() != 0 {
        return;
    }
    arch::pend_switch_context();
}

pub fn wake_up_all(mut w: SpinLockGuard<'_, WaitQueue>) -> usize {
    #[cfg(debugging_scheduler)]
    crate::trace!("[TH:0x{:x}] is waking up all threads", current_thread_id());
    let woken = wait_queue::wake_up_all(&mut w);
    drop(w);
    if woken > 0 {
        yield_me_now_or_later();
    }
    woken
}

pub fn is_schedule_ready() -> bool {
    READY_CORES.load(Ordering::Acquire) != 0
}

pub fn wait_and_then_start_schedule() {
    while READY_CORES.load(Ordering::Acquire) == 0 {
        core::hint::spin_loop();
    }
    arch::start_schedule(schedule);
}

// Entry of system idle threads.
pub extern "C" fn schedule() -> ! {
    READY_CORES.fetch_add(1, Ordering::Relaxed);
    arch::enable_local_irq();
    debug_assert!(arch::local_irq_enabled());
    loop {
        yield_me();
        idle::get_idle_hook()();
    }
}

#[inline]
pub fn current_thread() -> ThreadNode {
    let _guard = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    let t = unsafe { RUNNING_THREADS[my_id].assume_init_ref().clone() };
    t
}

#[inline]
pub fn current_thread_ref() -> &'static Thread {
    let _guard = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    unsafe { RUNNING_THREADS[my_id].assume_init_ref() }
}

#[inline]
pub fn current_thread_id() -> usize {
    let _guard = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    let t = unsafe { RUNNING_THREADS[my_id].assume_init_ref() };
    Thread::id(t)
}

pub(crate) fn need_reschedule_at(moment: Tick) -> bool {
    #[cfg(not(robin_scheduler))]
    return false;
    #[cfg(robin_scheduler)]
    {
        let this_thread = current_thread_ref();
        if Thread::id(this_thread) == Thread::id(idle::current_idle_thread_ref()) {
            return false;
        }
        let start = this_thread.this_round_start_at();
        let elapsed = start.since(moment);
        elapsed.0 >= this_thread.remaining_time_slices().0
    }
}

fn set_current_thread(t: ThreadNode) -> ThreadNode {
    let _dig = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    let old = unsafe { core::mem::replace(RUNNING_THREADS[my_id].assume_init_mut(), t) };
    // Do not validate sp here, since we might be using system stack,
    // like on cortex-m platform.
    old
}

// FIXME: Might use ArcCas to store Arc<Thread> in RUNNING_THREADS and
// IDLE_THREADS to avoid data race condition.
pub(crate) fn is_idle_core(id: usize) -> bool {
    let running = unsafe { RUNNING_THREADS[id].assume_init_ref() };
    let idle = unsafe { idle::IDLE_THREADS[id].assume_init_ref() };
    Thread::id(running) == Thread::id(idle)
}

pub(crate) fn notify_idle_cores(how_many: usize) {
    let this = arch::current_cpu_id();
    let mut notified = 0;
    for i in 0..NUM_CORES {
        if this == i || !is_idle_core(i) {
            continue;
        }
        arch::send_ipi(i);
        notified += 1;
        if notified == how_many {
            break;
        }
    }
}
