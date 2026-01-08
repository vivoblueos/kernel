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
    time::{
        self,
        timer::{Timer, TimerEntry},
        WAITING_FOREVER,
    },
    types::{Arc, IlistHead, Uint},
};
use alloc::boxed::Box;
use blueos_kconfig::CONFIG_NUM_CORES as NUM_CORES;
use core::{
    intrinsics::unlikely,
    mem::MaybeUninit,
    sync::atomic::{compiler_fence, AtomicBool, AtomicU8, Ordering},
};

mod global_scheduler;
mod idle;
pub use idle::{
    current_idle_thread, current_idle_thread_ref, get_idle_thread, get_idle_thread_ref,
};
pub(crate) mod wait_queue;

pub use global_scheduler::*;
pub(crate) use wait_queue::*;
static READY_CORES: AtomicU8 = AtomicU8::new(0);

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

pub(crate) static mut RUNNING_THREADS: [MaybeUninit<ThreadNode>; NUM_CORES as usize] =
    [const { MaybeUninit::zeroed() }; NUM_CORES as usize];

pub(crate) fn init() {
    idle::init_idle_threads();
    global_scheduler::init();
}

pub(crate) struct ContextSwitchHookHolder {
    next_thread: *const Thread,
    closure: Option<Box<dyn FnOnce()>>,
}

impl ContextSwitchHookHolder {
    pub fn new(next_thread: ThreadNode) -> Self {
        Self {
            next_thread: unsafe { Arc::into_raw(next_thread) },
            closure: None,
        }
    }

    pub fn set_closure(&mut self, closure: Box<dyn FnOnce()>) -> &mut Self {
        self.closure = Some(closure);
        self
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
    let closure = hook.closure.take();
    let next_saved_sp = spin_until_ready_to_run(&next);
    let ok = next.transfer_state(thread::READY, thread::RUNNING);
    debug_assert!(ok);
    // FIXME: Statistics of cycles should be optional.
    let cycles = time::get_sys_cycles();
    next.lock().set_start_cycles(cycles);
    // FIXME: Signal feature should be optional.
    {
        if next.lock().has_pending_signals() {
            prepare_signal_handling(&next);
        }
    }
    let next_id = Thread::id(&next);
    let next_saved_sp = next.saved_sp();
    let next_priority = next.priority();
    let mut old = set_current_thread(next);
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
    // FIXME: Statistics of cycles should be optional.
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
    compiler_fence(Ordering::SeqCst);
    if let Some(f) = closure {
        f()
    }
    old.set_saved_sp(old_sp);
    current_thread_ref().clear_saved_sp();
    next_saved_sp
}

fn switch_current_thread(next: ThreadNode, old_sp: usize) -> usize {
    let next_saved_sp = spin_until_ready_to_run(&next);
    let ok = next.transfer_state(thread::READY, thread::RUNNING);
    debug_assert!(ok);
    let next_id = Thread::id(&next);
    let next_priority = next.priority();
    // FIXME: Statistics of cycles should be optional.
    let cycles = time::get_sys_cycles();
    next.lock().set_start_cycles(cycles);
    let old = set_current_thread(next);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[PENDSV] Switching from 0x{:x}: {{ SP: 0x{:x} PRI: {} }} to 0x{:x}: {{ SP: 0x{:x} PRI: {} }}",
        Thread::id(&old),
        old.saved_sp(),
        old.priority(),
        next_id,
        next_saved_sp,
        next_priority,
    );
    // FIXME: Statistics of cycles should be optional.
    old.lock().increment_cycles(cycles);
    if Thread::id(&old) == Thread::id(idle::current_idle_thread_ref()) {
        let ok = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert!(ok);
    } else {
        let ok = queue_ready_thread(thread::RUNNING, old.clone());
        debug_assert!(ok);
    }
    old.set_saved_sp(old_sp);
    current_thread_ref().clear_saved_sp();
    next_saved_sp
}

// It's usually used in cortex-m's pendsv handler. It assumes current
// thread's context is already saved.
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
    switch_current_thread(next, old_sp)
}

pub fn retire_me() -> ! {
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
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
    debug_assert!(ok);
    arch::switch_context_with_hook(&mut hooks as *mut _);
    unreachable!("Retired thread should not reach here")
}

fn inner_yield(next: ThreadNode) {
    let old = current_thread();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    old.disable_preempt();
    let ok = if Thread::id(&old) == Thread::id(idle::current_idle_thread_ref()) {
        old.transfer_state(thread::RUNNING, thread::READY)
    } else {
        queue_ready_thread(thread::RUNNING, old.clone())
    };
    debug_assert!(ok);
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
        arch::idle();
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

fn setup_timer(
    thread: &ThreadNode,
    ticks: usize,
    hook_holder: &mut ContextSwitchHookHolder,
) -> Arc<AtomicBool> {
    let timeout = Arc::new(AtomicBool::new(false));
    let callback_closure = {
        let timeout = timeout.clone();
        let thread = thread.clone();
        move || {
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "Add thread 0x{:x} to ready queue after {} ticks",
                Thread::id(&thread),
                ticks,
            );
            queue_ready_thread_with_post_action(thread::SUSPENDED, thread, || {
                timeout.store(true, Ordering::Release)
            });
        }
    };
    let timeout_callback = TimerEntry::Once(Box::new(callback_closure));
    let hook_closure = {
        let thread = thread.clone();
        move || {
            if let Some(tm) = &thread.timer {
                tm.set_callback(timeout_callback);
                tm.start_new_interval(ticks);
            } else {
                let tm = Timer::new_hard_oneshot(ticks, timeout_callback);
                thread.lock().timer = Some(tm.clone());
                compiler_fence(Ordering::SeqCst);
                tm.start();
            };
        }
    };
    let hook = Box::new(hook_closure);
    hook_holder.set_closure(hook);
    timeout
}

pub(crate) fn suspend_me_with_hook(hook: impl FnOnce() + 'static) {
    if unlikely(!is_schedule_ready()) {
        return;
    }
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
    let old = current_thread_ref();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    let hook = Box::new(hook);
    hook_holder.set_closure(hook);
    old.disable_preempt();
    let ok = old.transfer_state(thread::RUNNING, thread::SUSPENDED);
    debug_assert!(ok);
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
    debug_assert!(arch::local_irq_enabled());
    // Shall we put enable_preempt in save_context_finish_hook?
    old.enable_preempt();
}

pub fn suspend_me_for(ticks: usize) {
    if unlikely(!is_schedule_ready()) {
        return;
    }
    debug_assert_ne!(ticks, 0);
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
    let old = current_thread_ref();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    if ticks != WAITING_FOREVER {
        setup_timer(&current_thread(), ticks, &mut hook_holder);
    }
    old.disable_preempt();
    let ok = old.transfer_state(thread::RUNNING, thread::SUSPENDED);
    debug_assert!(ok);
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
}

pub fn suspend_me_with_timeout(w: SpinLockGuard<'_, WaitQueue>, ticks: usize) -> bool {
    debug_assert_ne!(ticks, 0);
    if unlikely(!is_schedule_ready()) {
        return false;
    }
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] is looking for the next thread",
        current_thread_id()
    );
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
    debug_assert_eq!(next.state(), thread::READY);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] next thread is 0x{:x}",
        current_thread_id(),
        Thread::id(&next)
    );
    let old = current_thread_ref();
    // old's context saving must happen before old is requeued to
    // ready queue.
    // Ideally, we need an API like
    // ```
    // switch_context(from_sp_mut, to_sp, w)
    // ```
    // which is hard to implement in Rust. So we wrap all guards
    // inside a hook hodler and pass it by its
    // pointer. save_context_finish_hook is called during
    // switching context.
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    let timeout = if ticks != WAITING_FOREVER {
        setup_timer(&current_thread(), ticks, &mut hook_holder)
    } else {
        Arc::new(AtomicBool::new(false))
    };
    old.disable_preempt();
    let ok = old.transfer_state(thread::RUNNING, thread::SUSPENDED);
    debug_assert!(ok);
    drop(w);
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
    timeout.load(Ordering::Acquire)
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

pub(crate) fn handle_tick_increment(elapsed_ticks: usize) -> bool {
    #[cfg(robin_scheduler)]
    {
        let this_thread = current_thread_ref();
        if Thread::id(this_thread) != Thread::id(idle::current_idle_thread_ref())
            && this_thread.round_robin(elapsed_ticks) <= 0
            && this_thread.is_preemptable()
        {
            this_thread.reset_robin();
            return true;
        }
    }
    false
}

fn set_current_thread(t: ThreadNode) -> ThreadNode {
    let _dig = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    let old = unsafe { core::mem::replace(RUNNING_THREADS[my_id].assume_init_mut(), t) };
    // Do not validate sp here, since we might be using system stack,
    // like on cortex-m platform.
    old
}
