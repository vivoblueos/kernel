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
    support::DisableInterruptGuard,
    sync::SpinLockGuard,
    thread,
    thread::{Entry, GlobalQueueVisitor, Thread, ThreadNode},
    time::{self, timer::Timer, WAITING_FOREVER},
    types::{Arc, IlistHead},
};
use alloc::boxed::Box;
use blueos_kconfig::NUM_CORES;
use core::{
    mem::MaybeUninit,
    sync::atomic::{compiler_fence, AtomicBool, Ordering},
};

#[cfg(scheduler = "fifo")]
mod fifo;
#[cfg(scheduler = "global")]
mod global_scheduler;
mod idle;
pub use idle::get_idle_thread;
mod wait_queue;

#[cfg(scheduler = "fifo")]
pub use fifo::*;
#[cfg(scheduler = "global")]
pub use global_scheduler::*;
pub(crate) use wait_queue::*;

pub(crate) static mut RUNNING_THREADS: [MaybeUninit<ThreadNode>; NUM_CORES] =
    [const { MaybeUninit::zeroed() }; NUM_CORES];

pub(crate) fn init() {
    idle::init_idle_threads();
    #[cfg(scheduler = "global")]
    global_scheduler::init();
    #[cfg(scheduler = "fifo")]
    fifo::init();
}

pub(crate) struct ContextSwitchHookHolder<'a> {
    // Next thread is a must.
    pub next_thread: Option<ThreadNode>,
    pub ready_thread: Option<ThreadNode>,
    pub retiring_thread: Option<ThreadNode>,
    pub pending_thread: Option<ThreadNode>,
    pub closure: Option<Box<dyn FnOnce()>>,
    pub dropper: Option<DefaultWaitQueueGuardDropper<'a>>,
}

impl<'a> ContextSwitchHookHolder<'a> {
    pub fn new(next_thread: ThreadNode) -> Self {
        Self {
            next_thread: Some(next_thread),
            ready_thread: None,
            retiring_thread: None,
            pending_thread: None,
            closure: None,
            dropper: None,
        }
    }

    pub fn set_dropper(&mut self, d: DefaultWaitQueueGuardDropper<'a>) -> &mut Self {
        self.dropper = Some(d);
        self
    }

    pub fn set_ready_thread(&mut self, t: ThreadNode) -> &mut Self {
        self.ready_thread = Some(t);
        self
    }

    pub fn set_pending_thread(&mut self, t: ThreadNode) -> &mut Self {
        self.pending_thread = Some(t);
        self
    }

    pub fn set_retiring_thread(&mut self, t: ThreadNode) -> &mut Self {
        self.retiring_thread = Some(t);
        self
    }

    pub fn set_closure(&mut self, closure: Box<dyn FnOnce()>) -> &mut Self {
        self.closure = Some(closure);
        self
    }
}

// Must use next's thread's stack or system stack to exeucte this function.
// We assume this hook is invoked with local irq disabled.
// FIXME: rustc miscompiles it if inlined.
#[inline(never)]
pub(crate) extern "C" fn save_context_finish_hook(hook: Option<&mut ContextSwitchHookHolder>) {
    let Some(hook) = hook else {
        return;
    };
    // We must be careful that the last use of the `hook` must
    // happen-before enqueueing the ready thread to the ready queue,
    // since the `hook` is still on the stack of the ready thread. To
    // resolve race condition of the stack, we first take the
    // ownership of all pending actions in the `hook`, so that these
    // actions are on current stack.
    let ready_thread = hook.ready_thread.take();
    let retiring_thread = hook.retiring_thread.take();
    let closure = hook.closure.take();
    let pending_thread = hook.pending_thread.take();
    let mut dropper = hook.dropper.take();
    let next = hook.next_thread.take();
    compiler_fence(Ordering::SeqCst);
    let Some(mut next) = next else {
        panic!("Next thread must be specified!");
    };
    {
        let ok = next.transfer_state(thread::READY, thread::RUNNING);
        assert!(ok);
        let mut old = set_current_thread(next.clone());
        #[cfg(debugging_scheduler)]
        crate::trace!(
            "Switching from 0x{:x}: {{ SP: 0x{:x} PRI: {} }} to 0x{:x}: {{ SP: 0x{:x} PRI: {} }}",
            Thread::id(&old),
            old.saved_sp(),
            old.priority(),
            Thread::id(&next),
            next.saved_sp(),
            next.priority(),
        );

        let cycles = time::get_sys_cycles();
        old.lock().increment_cycles(cycles);
        next.lock().set_start_cycles(cycles);
    }
    compiler_fence(Ordering::SeqCst);
    if let Some(t) = ready_thread {
        let ok = crate::scheduler::queue_ready_thread(thread::RUNNING, t);
        assert!(ok);
    }
    compiler_fence(Ordering::SeqCst);
    if let Some(t) = pending_thread {
        let ok = t.transfer_state(thread::RUNNING, thread::SUSPENDED);
        assert!(ok);
    }
    compiler_fence(Ordering::SeqCst);
    // Local irq is disabled by arch and the scheduler assumes every thread
    // should be resumed with local irq enabled. Alternative solution to handle
    // irq status might be `save_context_finish_hook` taking an additional
    // irq_status arg indicating the irq status when entered the context switch
    // routine, and returning irq status indicating the irq status after leaving
    // the context switch routine.
    if let Some(v) = dropper.as_mut() {
        v.forget_irq()
    }
    drop(dropper);
    compiler_fence(Ordering::SeqCst);
    if let Some(f) = closure {
        f()
    }
    compiler_fence(Ordering::SeqCst);
    if let Some(t) = retiring_thread {
        let cleanup = t.lock().take_cleanup();
        if let Some(entry) = cleanup {
            match entry {
                Entry::C(f) => f(),
                Entry::Closure(f) => f(),
                Entry::Posix(f, arg) => f(arg),
            }
        };
        GlobalQueueVisitor::remove(&t);
        let ok = t.transfer_state(thread::RUNNING, thread::RETIRED);
        assert!(ok);
        if ThreadNode::strong_count(&t) != 1 {
            // TODO: Warn if there are still references to the thread.
        }
    }
}

// It's usually used in cortex-m's pendsv handler. It assumes current
// thread's context is already saved.
pub(crate) extern "C" fn yield_me_and_return_next_sp(old_sp: usize) -> usize {
    assert!(!arch::local_irq_enabled());
    let Some(next) = next_ready_thread() else {
        #[cfg(debugging_scheduler)]
        crate::trace!("[TH:0x{:x}] keeps running", current_thread_id());
        return old_sp;
    };
    let to_sp = next.saved_sp();
    let ok = next.transfer_state(thread::READY, thread::RUNNING);
    assert!(ok);
    let old = set_current_thread(next.clone());
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[PENDSV] Switching from 0x{:x}: {{ SP: 0x{:x} PRI: {} }} to 0x{:x}: {{ SP: 0x{:x} PRI: {} }}",
        Thread::id(&old),
        old.saved_sp(),
        old.priority(),
        Thread::id(&next),
        next.saved_sp(),
        next.priority(),
    );
    old.lock().set_saved_sp(old_sp);
    let ok = queue_ready_thread(thread::RUNNING, old);
    assert!(ok);
    to_sp
}

pub fn retire_me() -> ! {
    let next = next_ready_thread().map_or_else(|| idle::current_idle_thread().clone(), |v| v);
    let to_sp = next.saved_sp();

    let old = current_thread();
    #[cfg(procfs)]
    {
        let _ = crate::vfs::trace_thread_close(old.clone());
    }
    // FIXME: Some WaitQueue might still share the ownership of
    // the `old`, shall we record which WaitQueue the `old`
    // belongs to? Weak reference might not help to reduce memory
    // usage.
    let mut hooks = ContextSwitchHookHolder::new(next);
    hooks.set_retiring_thread(old);
    arch::restore_context_with_hook(to_sp, &mut hooks as *mut _);
}

pub fn yield_me() {
    // We don't allow thread yielding with irq disabled.
    // The scheduler assumes every thread should be resumed with local
    // irq enabled.
    assert!(arch::local_irq_enabled());
    let pg = thread::Thread::try_preempt_me();
    if !pg.preemptable() {
        arch::idle();
        return;
    }
    drop(pg);
    yield_unconditionally();
}

fn yield_unconditionally() {
    assert!(arch::local_irq_enabled());
    let Some(next) = next_ready_thread() else {
        arch::idle();
        return;
    };
    let to_sp = next.saved_sp();
    let old = current_thread();
    let from_sp_ptr = old.saved_sp_ptr();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    if Thread::id(&old) == Thread::id(idle::current_idle_thread()) {
        let ok = old.transfer_state(thread::RUNNING, thread::READY);
        assert!(ok);
        drop(old);
        // We should never put idle thread to ready queue.
        arch::switch_context_with_hook(from_sp_ptr as *mut u8, to_sp, &mut hook_holder as *mut _);
    } else {
        hook_holder.set_ready_thread(old);
        arch::switch_context_with_hook(from_sp_ptr as *mut u8, to_sp, &mut hook_holder as *mut _);
    }
    assert!(arch::local_irq_enabled());
}

pub(crate) fn suspend_me_with_hook(hook: impl FnOnce() + 'static) {
    let next = next_ready_thread().map_or_else(|| idle::current_idle_thread().clone(), |v| v);
    let to_sp = next.saved_sp();
    let old = current_thread();
    let from_sp_ptr = old.saved_sp_ptr();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    let hook = Box::new(hook);
    hook_holder.set_closure(hook);
    arch::switch_context_with_hook(from_sp_ptr as *mut u8, to_sp, &mut hook_holder as *mut _);
    assert!(arch::local_irq_enabled());
}

pub(crate) fn suspend_me_for(tick: usize) {
    assert!(tick != 0);
    let next = next_ready_thread().map_or_else(|| idle::current_idle_thread().clone(), |v| v);
    let to_sp = next.saved_sp();
    let old = current_thread();
    let from_sp_ptr = old.saved_sp_ptr();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    hook_holder.set_pending_thread(old.clone());

    if tick != WAITING_FOREVER {
        let th = old.clone();
        let timer_callback = Box::new(move || {
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "Add thread 0x{:x} to ready queue after timeout",
                Thread::id(&th)
            );
            let _ = queue_ready_thread(thread::SUSPENDED, th.clone());
        });
        let hook = Box::new(move || {
            match &old.timer {
                Some(t) => {
                    t.set_callback(timer_callback);
                    t.start_new_interval(tick);
                }
                None => {
                    let timer = Timer::new_hard_oneshot(tick, timer_callback);
                    old.lock().timer = Some(timer.clone());
                    compiler_fence(Ordering::SeqCst);
                    timer.start();
                }
            };
        });
        hook_holder.set_closure(hook);
    }

    arch::switch_context_with_hook(from_sp_ptr as *mut u8, to_sp, &mut hook_holder as *mut _);
    assert!(arch::local_irq_enabled());
}

pub(crate) fn suspend_me_with_timeout(mut w: SpinLockGuard<'_, WaitQueue>, ticks: usize) -> bool {
    assert!(ticks != 0);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] is looking for the next thread",
        current_thread_id()
    );
    let next = next_ready_thread().map_or_else(|| idle::current_idle_thread().clone(), |v| v);
    #[cfg(debugging_scheduler)]
    crate::trace!(
        "[TH:0x{:x}] next thread is 0x{:x}",
        current_thread_id(),
        Thread::id(&next)
    );
    // FIXME: Ideally, we should defer state transfer to context switch hook.
    let to_sp = next.saved_sp();
    let old = current_thread();
    let from_sp_ptr = old.saved_sp_ptr();
    let entry = Arc::new(WaitEntry {
        wait_node: IlistHead::<WaitEntry, OffsetOfWait>::new(),
        thread: old.clone(),
    });
    let ok = w.push_back(entry);
    assert!(ok);
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
    let mut dropper = DefaultWaitQueueGuardDropper::new();
    dropper.add(w);
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    hook_holder.set_dropper(dropper);
    hook_holder.set_pending_thread(old.clone());
    let timed_out = Arc::new(AtomicBool::new(false));
    let timed_out_clone = timed_out.clone();

    if ticks != WAITING_FOREVER {
        let th = old.clone();
        let timer_callback = Box::new(move || {
            #[cfg(debugging_scheduler)]
            crate::trace!(
                "Add thread 0x{:x} to ready queue after timeout",
                Thread::id(&th)
            );
            let _ = queue_ready_thread(thread::SUSPENDED, th.clone());
            timed_out_clone.store(true, Ordering::SeqCst);
        });
        let hook = Box::new(move || {
            match &old.timer {
                Some(t) => {
                    t.set_callback(timer_callback);
                    t.start_new_interval(ticks);
                }
                None => {
                    let timer = Timer::new_hard_oneshot(ticks, timer_callback);
                    old.lock().timer = Some(timer.clone());
                    compiler_fence(Ordering::SeqCst);
                    timer.start();
                }
            };
        });
        hook_holder.set_closure(hook);
    }
    arch::switch_context_with_hook(from_sp_ptr as *mut u8, to_sp, &mut hook_holder as *mut _);
    assert!(arch::local_irq_enabled());
    timed_out.load(Ordering::SeqCst)
}

// Yield me immediately if not in ISR, otherwise switch context on
// exiting of the inner most ISR. Or just do nothing if underling arch
// doesn't have good support of this semantics. Cortex-m's pendsv is
// perfectly meet this semantics.
pub(crate) fn yield_me_now_or_later() {
    arch::pend_switch_context();
}

// Entry of system idle threads.
pub(crate) extern "C" fn schedule() -> ! {
    #[cfg(debugging_scheduler)]
    crate::trace!("Start scheduling");

    arch::enable_local_irq();
    assert!(arch::local_irq_enabled());
    loop {
        yield_me();
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
pub fn current_thread_id() -> usize {
    let _guard = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    let t = unsafe { RUNNING_THREADS[my_id].assume_init_ref() };
    Thread::id(t)
}

pub(crate) fn handle_tick_increment(elapsed_ticks: usize) -> bool {
    #[cfg(robin_scheduler)]
    {
        let th = current_thread();
        if Thread::id(&th) != Thread::id(idle::current_idle_thread())
            && th.round_robin(elapsed_ticks) <= 0
            && th.is_preemptable()
        {
            th.reset_robin();
            return true;
        }
    }
    false
}

fn set_current_thread(t: ThreadNode) -> ThreadNode {
    let _dig = DisableInterruptGuard::new();
    let my_id = arch::current_cpu_id();
    assert!(t.validate_saved_sp());
    let old = unsafe { core::mem::replace(RUNNING_THREADS[my_id].assume_init_mut(), t) };
    // Do not validate sp here, since we might be using system stack,
    // like on cortex-m platform.
    old
}
