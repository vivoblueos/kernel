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
#[cfg(event_flags)]
use crate::sync::event_flags::EventFlagsMode;
use crate::{
    arch,
    arch::Context,
    config,
    config::DEFAULT_STACK_SIZE,
    debug,
    process::Process,
    scheduler,
    support::{Region, RegionalObjectBuilder, Storage},
    sync::{
        mutex::{MutexList, MutexListIterator},
        ISpinLock, Mutex, SpinLock, SpinLockGuard, SpinLockReadGuard, SpinLockWriteGuard,
    },
    thread::builder::GlobalQueue,
    time::Tick,
    types::{
        impl_simple_intrusive_adapter, Arc, ArcCas, ArcList, ArcListIterator, AtomicUint,
        GenericList, IlistHead, ThreadPriority, Uint, UniqueListHead,
    },
};
use alloc::{boxed::Box, sync::Weak};
use blueos_infra::no_let_underscore::IgnoreResult;
use core::{
    alloc::Layout,
    cell::Cell,
    ptr::NonNull,
    sync::atomic::{AtomicI32, AtomicUsize, Ordering},
};

mod builder;
pub use builder::*;

/// Bumped whenever the world may have made a polled file descriptor ready.
///
/// `poll()` reads this before scanning, then blocks on it only while the
/// value is unchanged. Anything that changes descriptor state - the network
/// stack after a pass over the interfaces, or a signal arriving for a thread
/// that is asleep in `poll()` - increments it and wakes waiters, so a poller
/// cannot miss a transition that happens between its scan and its sleep: if
/// the counter moved in that window the wait returns immediately and the
/// scan runs again.
///
/// It lives here rather than in the poll code so that the signal path can
/// reach it without depending on the VFS, which some targets leave out.
pub static POLL_EPOCH: AtomicUsize = AtomicUsize::new(0);

/// Announces that a descriptor may have become ready.
pub fn bump_poll_epoch() {
    POLL_EPOCH.fetch_add(1, Ordering::Release);
    crate::sync::atomic_wait::atomic_wake(&POLL_EPOCH, usize::MAX).ignore_result();
}

/// The current epoch value, for a poller to compare against after scanning.
pub fn poll_epoch() -> usize {
    POLL_EPOCH.load(Ordering::Acquire)
}

pub type ThreadNode = Arc<Thread>;

pub enum Entry {
    C(extern "C" fn()),
    Posix(
        extern "C" fn(*mut core::ffi::c_void),
        *mut core::ffi::c_void,
    ),
    Closure(Box<dyn FnOnce()>),
}

impl core::fmt::Debug for Entry {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        Ok(())
    }
}

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
pub enum ThreadKind {
    AsyncPoller,
    Idle,
    #[default]
    Normal,
    #[cfg(soft_timer)]
    SoftTimer,
}

#[derive(Debug)]
pub struct Stack(Storage);

impl Stack {
    #[inline]
    pub fn top(&self) -> *mut u8 {
        unsafe { self.0.base().add(self.size()) }
    }

    #[inline]
    pub fn base(&self) -> *mut u8 {
        self.0.base()
    }

    #[inline]
    pub fn from_size(size: usize) -> Option<Self> {
        let layout = Layout::from_size_align(size, core::mem::align_of::<Context>()).ok()?;
        let storage = Storage::from_layout(layout);
        // Storage::from_layout does not check for allocation failure (it returns
        // a Storage holding a null base). Detect that here so callers can fail
        // gracefully via Option instead of silently creating a thread with a
        // null stack, which would crash/hang the scheduler with no diagnostics.
        if storage.base().is_null() {
            return None;
        }
        Some(Self(storage))
    }

    pub const fn new() -> Self {
        Self(Storage::new())
    }

    #[inline]
    pub fn from_raw(base: *mut u8, size: usize) -> Option<Self> {
        const ALIGN: usize = core::mem::align_of::<Context>();
        if size < ALIGN {
            return None;
        }
        if base.is_null() {
            return None;
        }
        if !(base as usize).is_multiple_of(ALIGN) {
            return None;
        }
        Some(Self(unsafe { Storage::from_raw(base, size) }))
    }

    pub fn size(&self) -> usize {
        self.0.size()
    }
}

impl_simple_intrusive_adapter!(OffsetOfSchedNode, Thread, sched_node);
impl_simple_intrusive_adapter!(OffsetOfGlobal, Thread, global);
impl_simple_intrusive_adapter!(OffsetOfLock, Thread, lock);
impl_simple_intrusive_adapter!(OffsetOfProcessNode, Thread, process_node);

// Intrusive list of the threads owned by a process.
pub(crate) type ThreadList = ArcList<Thread, OffsetOfProcessNode>;
pub(crate) type ThreadListIterator<'a> = ArcListIterator<'a, Thread, OffsetOfProcessNode>;
pub(crate) type ThreadListNode = <ThreadList as GenericList>::Node;

// When a thread is created or is removed from the RQ.
pub const IDLE: Uint = 0;
// When a thread is added to a RQ.
pub const READY: Uint = 1;
// When a thread is running.
pub const RUNNING: Uint = 2;
// When a thread is suspended.
pub const SUSPENDED: Uint = 3;
// When a thread is retired.
pub const RETIRED: Uint = 4;

// ThreadStats is protected by thread scheduler.
#[derive(Debug, Default)]
pub struct ThreadStats {
    start: Cell<u64>,
    cycles: Cell<u64>,
}

impl ThreadStats {
    pub const fn new() -> Self {
        Self {
            start: Cell::new(0),
            cycles: Cell::new(0),
        }
    }

    pub fn increment_cycles(&self, cycles: u64) {
        let cycles = self.get_cycles();
        self.cycles
            .set(cycles + cycles.saturating_sub(self.start.get()));
    }

    pub fn set_start_cycles(&self, start: u64) {
        self.start.set(start);
    }

    pub fn start_cycles(&self) -> u64 {
        self.start.get()
    }

    pub fn get_cycles(&self) -> u64 {
        self.cycles.get()
    }
}

pub(crate) type GlobalQueueListHead = UniqueListHead<Thread, OffsetOfGlobal, GlobalQueue>;

#[derive(Default)]
pub(crate) struct SignalContext {
    // The set of signals that have been delivered to this thread but not
    // yet handled. An atomic so that a thread can be inspected through a
    // shared reference - `sigpending()` and the delivery path both need to
    // look at another thread's pending set.
    pending_signals: core::sync::atomic::AtomicU32,
    active: bool,
    // Will recover thread_context at recover_sp on exiting of signal handler.
    recover_sp: usize,
    thread_context: arch::Context,
    once_action: [Option<Box<dyn FnOnce()>>; 32],
}

impl core::fmt::Debug for SignalContext {
    fn fmt(&self, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Ok(())
    }
}

#[derive(Debug)]
pub struct Thread {
    global: GlobalQueueListHead,
    sched_node: IlistHead<Thread, OffsetOfSchedNode>,
    // Cleanup function will be invoked when retiring.
    cleanup: Option<Entry>,
    kind: ThreadKind,
    // Thread owns Stack::Alloc. It calls dealloc when dropping its self.
    stack: Stack,
    // If saved_sp is 0, the thread should be in RUNNING state. Otherwise, it's
    // switching context or is in a non RUNNING state.
    saved_sp: AtomicUsize,
    // This value may change at runtime.
    priority: ThreadPriority,
    // This is the static priority of this thread.
    origin_priority: ThreadPriority,
    state: AtomicUint,
    preempt_count: AtomicUint,
    // FIXME: Using a rusty lock looks not flexible. Now we are using
    // a C-style intrusive lock. It's conventional to declare which
    // fields this lock is protecting. lock is protecting the
    // whole struct except those atomic fields.
    lock: ISpinLock<Thread, OffsetOfLock>,
    #[cfg(thread_stats)]
    stats: ThreadStats,
    #[cfg(event_flags)]
    event_flags_mode: EventFlagsMode,
    #[cfg(event_flags)]
    event_flags_mask: u32,
    // An opaque pointer used by C extensions. Must be noted, these C extensions
    // are aware of kernel's APIs, while POSIX are not. So librs' POSIX
    // implementation should not rely on this field.
    alien_ptr: Option<NonNull<core::ffi::c_void>>,
    // The mutex this thread is acquiring.
    pending_on_mutex: ArcCas<Mutex>,
    // Mutexes this thread has acquired.  It's protected by its own spinlock to
    // avoid deadlock, since before this change we might have lock pattern
    // Thread0:
    // - Lock mutex's spinlock
    // - Lock this thread
    // - Change priority
    // Thread1:
    // - Lock this thread
    // - Iterate over acquired mutexes
    // - Lock mutex's spinlock
    // - Check mutex's pending queue
    acquired_mutexes: SpinLock<MutexList>,
    signal_context: Option<Box<SignalContext>>,
    // The set of signals this thread is currently blocking (`sigprocmask`).
    // Separate from `SignalContext`, which holds the *pending* set: the mask
    // is consulted at delivery time, the pending set records what arrived.
    signal_mask: crate::signal::posix::ThreadSignalMask,
    // A futex word that is woken whenever a signal is delivered to this
    // thread. `sigsuspend()` and `sigwait()` block on it, so a signal
    // arriving for a thread that is asleep has to wake it up.
    signal_futex: core::sync::atomic::AtomicUsize,
    // How many signals have had their disposition applied on this thread -
    // a user handler run, or the default action taken. `poll()` compares two
    // readings of this to tell that a signal was caught while it was asleep:
    // by the time the waiter is scheduled again the pending bit is already
    // clear and the handler has already run, so the pending set alone cannot
    // answer the question.
    signals_delivered: core::sync::atomic::AtomicUsize,
    // The `Context` this thread's most recent U-mode trap saved, or 0 when
    // that trap came from kernel mode. Signal delivery needs it to redirect
    // the eventual `mret` into a handler instead of calling the handler from
    // the kernel stack, which would run it with kernel privileges. It is not
    // cleared when the thread returns to U-mode: the frame stays valid until
    // the next trap overwrites it, and nested kernel-mode traps must not hide
    // the U-mode frame underneath.
    #[cfg(target_arch = "riscv64")]
    trap_frame: core::sync::atomic::AtomicUsize,
    // Set when a trap-frame signal delivery has rewritten `a0`/`mepc` in the
    // frame. The ecall return path would otherwise overwrite the handler
    // argument with the syscall result.
    #[cfg(target_arch = "riscv64")]
    signal_redirect: core::sync::atomic::AtomicBool,
    // A weak reference to the process this thread belongs to. Kernel/system
    // threads that are not owned by any process carry a dangling `Weak`
    // (constructed via `Weak::new()`, whose `upgrade()` returns `None`).
    process: Weak<Process>,
    // Intrusive node linking this thread into its owning process's thread
    // list. Protected by the process's `threads` spinlock.
    process_node: ThreadListNode,
    #[cfg(round_robin)]
    rr: RoundRobin,
    // Redirect written by `execve` and consumed by the trap layer when this
    // syscall returns. It lives on the thread, not in a global: with SMP, a
    // global slot let any other thread on any hart "return into" a program it
    // never exec'd — observed as a user fault at the new entry point with a
    // stale `satp`.
    #[cfg(target_arch = "riscv64")]
    pending_exec: SpinLock<Option<crate::user::ExecOutcome>>,
}

#[cfg(round_robin)]
#[derive(Default, Debug)]
pub(crate) struct RoundRobin {
    this_round_start_at: Cell<Tick>,
    time_slices: Cell<Tick>,
}

#[cfg(round_robin)]
impl RoundRobin {
    pub const fn new() -> Self {
        Self {
            this_round_start_at: Cell::new(Tick(0)),
            time_slices: Cell::new(Tick(0)),
        }
    }
}

extern "C" fn run_simple_c(f: extern "C" fn()) {
    f();
    scheduler::retire_me();
}

extern "C" fn run_posix(f: extern "C" fn(*mut core::ffi::c_void), arg: *mut core::ffi::c_void) {
    f(arg);
    scheduler::retire_me();
}

// FIXME: If the closure doesn't get run, memory leaks.
extern "C" fn run_closure(raw: *mut Box<dyn FnOnce()>) {
    // FIXME: If `retire_me` is called in the closure, we are unable to recycle
    // the Box and memory leaks.
    unsafe { Box::from_raw(raw)() };
    scheduler::retire_me();
}

impl Thread {
    #[cfg(thread_stats)]
    #[inline]
    pub fn stats(&self) -> &ThreadStats {
        &self.stats
    }

    // FIXME: rustc miscompiles it if not inlined.
    #[inline]
    pub fn lock(&self) -> SpinLockGuard<'_, Self> {
        self.lock.irqsave_lock()
    }

    #[inline]
    pub fn lock_for_read(&self) -> SpinLockReadGuard<'_, Self> {
        self.lock.irqsave_read()
    }

    #[inline(always)]
    pub fn stack_usage(&self) -> usize {
        let sp = arch::current_sp();
        self.stack.top() as usize - sp
    }

    #[inline(always)]
    pub fn validate_sp(&self) -> bool {
        let sp = arch::current_sp();
        sp >= self.stack.base() as usize && sp <= self.stack.top() as usize
    }

    #[inline(always)]
    pub fn saved_stack_usage(&self) -> usize {
        self.stack.top() as usize - self.saved_sp()
    }

    #[inline]
    pub fn stack_base(&self) -> usize {
        self.stack.base() as usize
    }

    #[inline]
    pub fn stack_size(&self) -> usize {
        self.stack.size()
    }

    #[inline]
    pub fn state(&self) -> Uint {
        self.state.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn state_to_str(&self) -> &str {
        let state = self.state.load(Ordering::Relaxed);
        match state {
            IDLE => "idle",
            READY => "ready",
            RUNNING => "running",
            SUSPENDED => "suspended",
            RETIRED => "retired",
            _ => "unknown",
        }
    }

    #[inline]
    pub fn kind(&self) -> ThreadKind {
        self.kind
    }

    #[inline]
    pub fn kind_to_str(&self) -> &str {
        match self.kind {
            ThreadKind::AsyncPoller => "async_poller",
            ThreadKind::Idle => "idle",
            ThreadKind::Normal => "normal",
            #[cfg(soft_timer)]
            ThreadKind::SoftTimer => "soft_timer",
        }
    }

    #[inline]
    pub fn transfer_state(&self, from: Uint, to: Uint) -> Result<(), Uint> {
        self.state
            .compare_exchange(from, to, Ordering::AcqRel, Ordering::Acquire)
            .map(|_| ())
    }

    #[inline]
    pub unsafe fn set_state(&self, to: Uint) -> &Self {
        self.state.store(to, Ordering::Relaxed);
        self
    }

    #[inline]
    pub fn set_priority(&mut self, p: ThreadPriority) -> &mut Self {
        self.priority = p;
        self
    }

    #[inline]
    pub fn set_kind(&mut self, kind: ThreadKind) -> &mut Self {
        self.kind = kind;
        self
    }

    #[inline]
    pub fn saved_sp(&self) -> usize {
        self.saved_sp.load(Ordering::Acquire)
    }

    #[inline]
    pub fn set_stack(&mut self, stack: Stack) -> &mut Self {
        self.stack = stack;
        self
    }

    #[inline]
    pub fn take_cleanup(&mut self) -> Option<Entry> {
        self.cleanup.take()
    }

    #[inline]
    pub fn set_cleanup(&mut self, cleanup: Entry) {
        self.cleanup = Some(cleanup);
    }

    #[inline]
    pub fn add_acquired_mutex(&self, mu: Arc<Mutex>) -> bool {
        self.acquired_mutexes.irqsave_write().push_back(mu)
    }

    #[inline]
    pub fn remove_acquired_mutex(&self, mu: &Arc<Mutex>) -> bool {
        self.acquired_mutexes
            .irqsave_write()
            .remove_if(|e| core::ptr::eq(Arc::as_ptr(mu), e))
            .is_some()
    }

    #[inline]
    pub fn has_acquired_mutex(&self) -> bool {
        !self.acquired_mutexes.irqsave_read().is_empty()
    }

    #[inline]
    pub fn acquired_mutexes_mut(&self) -> SpinLockWriteGuard<'_, MutexList> {
        self.acquired_mutexes.irqsave_write()
    }

    #[inline]
    pub fn replace_pending_on_mutex(&self, mu: Option<Arc<Mutex>>) -> Option<Arc<Mutex>> {
        self.pending_on_mutex.swap(mu, Ordering::Release)
    }

    pub fn process(&self) -> Option<alloc::sync::Arc<Process>> {
        self.process.upgrade()
    }

    /// Set the owning process. Called by `Process::add_thread`/
    /// `Process::remove_thread` while holding the thread's spinlock.
    pub fn set_process(&mut self, process: Weak<Process>) {
        self.process = process;
    }

    const fn new(kind: ThreadKind) -> Self {
        Self {
            cleanup: None,
            stack: Stack::new(),
            state: AtomicUint::new(IDLE),
            lock: ISpinLock::new(),
            sched_node: IlistHead::<Thread, OffsetOfSchedNode>::new(),
            global: UniqueListHead::new(),
            saved_sp: AtomicUsize::new(0),
            priority: 0,
            origin_priority: 0,
            preempt_count: AtomicUint::new(0),
            #[cfg(thread_stats)]
            stats: ThreadStats::new(),
            kind,
            #[cfg(event_flags)]
            event_flags_mode: EventFlagsMode::empty(),
            #[cfg(event_flags)]
            event_flags_mask: 0,
            alien_ptr: None,
            pending_on_mutex: ArcCas::new(None),
            acquired_mutexes: SpinLock::new(MutexList::new()),
            signal_context: None,
            signal_mask: crate::signal::posix::ThreadSignalMask::new(),
            signal_futex: core::sync::atomic::AtomicUsize::new(0),
            signals_delivered: core::sync::atomic::AtomicUsize::new(0),
            #[cfg(target_arch = "riscv64")]
            trap_frame: core::sync::atomic::AtomicUsize::new(0),
            #[cfg(target_arch = "riscv64")]
            signal_redirect: core::sync::atomic::AtomicBool::new(false),
            process: Weak::new(),
            process_node: ThreadListNode::new(),
            #[cfg(round_robin)]
            rr: RoundRobin::new(),
            #[cfg(target_arch = "riscv64")]
            pending_exec: SpinLock::new(None),
        }
    }

    /// Record the redirect produced by a successful `execve` on this thread.
    #[cfg(target_arch = "riscv64")]
    pub(crate) fn set_pending_exec(&self, outcome: crate::user::ExecOutcome) {
        *self.pending_exec.irqsave_lock() = Some(outcome);
    }

    /// Consume this thread's pending `execve` redirect, if any.
    #[cfg(target_arch = "riscv64")]
    pub fn take_pending_exec(&self) -> Option<crate::user::ExecOutcome> {
        self.pending_exec.irqsave_lock().take()
    }

    #[inline]
    pub fn id(me: &Self) -> usize {
        me as *const Self as usize
    }

    #[inline]
    pub(crate) fn try_preempt_me() -> PreemptGuard {
        let current = scheduler::current_thread();
        let status = current.disable_preempt();
        PreemptGuard { t: current, status }
    }

    #[inline]
    pub(crate) fn try_preempt(t: &ThreadNode) -> PreemptGuard {
        PreemptGuard {
            t: t.clone(),
            status: t.disable_preempt(),
        }
    }

    #[inline]
    pub fn is_preemptable(&self) -> bool {
        self.preempt_count.load(Ordering::Relaxed) == 0
    }

    #[inline]
    pub(crate) fn clear_saved_sp(&self) -> &Self {
        self.set_saved_sp(0);
        self
    }

    #[inline]
    pub(crate) fn reset_saved_sp(&self) -> &Self {
        self.set_saved_sp(self.stack.top() as usize);
        self
    }

    #[inline]
    pub(crate) fn set_saved_sp(&self, sp: usize) -> &Self {
        self.saved_sp.store(sp, Ordering::Release);
        self
    }

    #[inline]
    pub(crate) fn pending_on_mutex(&self) -> Option<Arc<Mutex>> {
        self.pending_on_mutex.load(Ordering::Acquire)
    }

    #[inline]
    fn get_or_create_signal_context(&mut self) -> &mut SignalContext {
        match self.signal_context {
            Some(ref mut ctx) => ctx,
            _ => {
                let mut ctx = Box::new(SignalContext::default());
                ctx.active = false;
                self.signal_context = Some(ctx);
                self.signal_context.as_mut().unwrap()
            }
        }
    }

    pub fn kill_with_once_handler(&mut self, signum: i32, f: impl FnOnce() + 'static) -> bool {
        if !self.kill(signum) {
            return false;
        }
        self.register_once_signal_handler(signum, f);
        true
    }

    pub fn kill(&mut self, signum: i32) -> bool {
        // Signal 0 does not exist and the pending set is 32 bits wide, so a
        // number outside `1..NSIG` cannot be marked pending. Callers reach
        // here either from a syscall that already validated the number or
        // from kernel code naming one of its own constants.
        if !crate::signal::posix::valid_signum(signum) {
            return false;
        }
        let flag = crate::signal::posix::bit(signum as usize);
        let sig_ctx = self.get_or_create_signal_context();
        let old = sig_ctx.pending_signals.load(core::sync::atomic::Ordering::Acquire);
        sig_ctx
            .pending_signals
            .fetch_or(flag as u32, core::sync::atomic::Ordering::AcqRel);
        // Return false if there is signum pending.
        //
        // Waking a sleeper is the *caller's* job and has to happen after the
        // thread lock is dropped: `wake_signal_waiters()` asks the scheduler
        // for a re-schedule, and this thread is normally inspected while its
        // lock - or the process's thread-list lock - is held, which runs with
        // interrupts disabled.
        (old as usize & flag) != 0
    }

    /// Wakes a thread that is waiting for a signal.
    ///
    /// The futex word is bumped so that a waiter blocked on the old value
    /// returns, and the word is reset so the next waiter blocks again.
    pub(crate) fn wake_signal_waiters(&self) {
        self.signal_futex
            .fetch_add(1, core::sync::atomic::Ordering::Release);
        crate::sync::atomic_wait::atomic_wake(&self.signal_futex, usize::MAX).ignore_result();
        // A signal also has to interrupt a thread that is sitting in
        // `poll()`, but the wake cannot happen here: this runs under the
        // thread lock, with interrupts off, and putting a thread back on the
        // ready queue is not legal from inside a critical section. The
        // callers that raise a signal do it once they have dropped the lock -
        // see `signal::posix::syscalls`.
    }

    /// The futex word a thread waits on for signal delivery.
    pub fn signal_futex(&self) -> &core::sync::atomic::AtomicUsize {
        &self.signal_futex
    }

    /// Records that a signal's disposition has just been applied on this
    /// thread. See the field comment for why `poll()` needs to count these.
    pub fn note_signal_delivered(&self) {
        self.signals_delivered
            .fetch_add(1, core::sync::atomic::Ordering::Release);
    }

    /// How many signals have been delivered to this thread so far.
    pub fn signals_delivered(&self) -> usize {
        self.signals_delivered
            .load(core::sync::atomic::Ordering::Acquire)
    }

    /// Records the trap frame of the most recent U-mode trap. Kernel-mode
    /// traps leave the previous value in place.
    #[cfg(target_arch = "riscv64")]
    pub fn set_trap_frame(&self, frame: usize) {
        self.trap_frame
            .store(frame, core::sync::atomic::Ordering::Release);
    }

    /// The trap frame recorded by the last U-mode trap, or 0.
    #[cfg(target_arch = "riscv64")]
    pub fn trap_frame(&self) -> usize {
        self.trap_frame.load(core::sync::atomic::Ordering::Acquire)
    }

    /// Marks that the saved frame now returns into a signal handler.
    #[cfg(target_arch = "riscv64")]
    pub fn set_signal_redirect(&self) {
        self.signal_redirect
            .store(true, core::sync::atomic::Ordering::Release);
    }

    /// Consumes the signal redirect, if any.
    #[cfg(target_arch = "riscv64")]
    pub fn take_signal_redirect(&self) -> bool {
        self.signal_redirect
            .swap(false, core::sync::atomic::Ordering::AcqRel)
    }

    /// Wakes a thread that is blocked in `poll()` / `ppoll()`.
    ///
    /// Called when a signal arrives for a thread that is asleep waiting for
    /// a descriptor: POSIX says `poll()` returns `EINTR` in that case rather
    /// than sleeping out its timeout. The wake goes through the global poll
    /// epoch, which is what `poll()` actually waits on.
    pub fn wake_poll_waiters(&self) {
        bump_poll_epoch();
    }

    pub fn register_once_signal_handler(&mut self, signum: i32, f: impl FnOnce() + 'static) {
        // The table is indexed by the signal number and has `NSIG` slots, so
        // an out-of-range number would index past the end.
        if !crate::signal::posix::valid_signum(signum) {
            return;
        }
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.once_action[signum as usize] = Some(Box::new(f));
    }

    pub fn take_signal_handler(&mut self, signum: i32) -> Option<Box<dyn FnOnce()>> {
        if !crate::signal::posix::valid_signum(signum) {
            return None;
        }
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.once_action[signum as usize].take()
    }

    pub(crate) fn activate_signal_context(&mut self) -> bool {
        let saved_sp = self.saved_sp();
        let sig_ctx = self.get_or_create_signal_context();
        // Nested signal handling is not supported.
        if sig_ctx.active {
            return false;
        }
        // Save the context being restored first.
        sig_ctx.recover_sp = saved_sp;
        let ctx = saved_sp as *const arch::Context;
        unsafe { core::ptr::copy(ctx, &mut sig_ctx.thread_context as *mut _, 1) };
        sig_ctx.active = true;
        true
    }

    fn is_in_signal_context(&self) -> bool {
        let Some(ref ctx) = self.signal_context else {
            return false;
        };
        ctx.active
    }

    pub(crate) fn deactivate_signal_context(&mut self) {
        let sig_ctx = self.get_or_create_signal_context();
        debug_assert!(sig_ctx.active);
        let saved_sp = sig_ctx.recover_sp;
        let ctx = saved_sp as *mut arch::Context;
        unsafe { core::ptr::copy(&sig_ctx.thread_context as *const _, ctx, 1) };
        sig_ctx.active = false;
        self.set_saved_sp(saved_sp);
    }

    pub(crate) fn signal_handler_sp(&mut self) -> usize {
        let saved_sp = self.saved_sp();
        debug_assert_eq!(saved_sp % core::mem::align_of::<Context>(), 0);
        saved_sp - core::mem::size_of::<Context>()
    }

    /// High address
    /// ------------------------------ <--- stack.top() == allocated buffer end
    /// | optional align gap (0..A)  |
    /// ------------------------------
    /// | Context for current thread |
    /// ------------------------------ <--- saved_sp (initial SP)
    /// |       stack region         |     (stack grows down)
    /// |           ...              |
    /// ------------------------------ <--- guard upper bound (if enabled)
    /// | stack guard region         |     (optional, usually no-access)
    /// ------------------------------ <--- stack.base()
    /// Low address
    /// FIXME: If an exception happens when SP is very close to (or already inside)
    /// the guard, hardware exception stacking (cortex-m) may touch this no-access region
    /// and trigger MemManage (for example DACCVIOL/MSTKERR); if fault handling
    /// cannot proceed, the fault may escalate to HardFault.
    pub(crate) fn init(&mut self, stack: Stack, entry: Entry) -> &mut Self {
        unsafe { self.set_state(IDLE) };
        self.stack = stack;
        // TODO: Stack sanity check.
        let maybe_sp = self.stack.top() as usize
            - (core::mem::size_of::<arch::Context>() + core::mem::align_of::<arch::Context>());
        self.acquired_mutexes.irqsave_write().init();

        let region = Region {
            base: maybe_sp,
            size: core::mem::size_of::<arch::Context>() + core::mem::align_of::<arch::Context>(),
        };
        let mut builder = RegionalObjectBuilder::new(region);
        let ctx = unsafe { builder.zeroed_after_start::<arch::Context>().unwrap() };
        self.set_saved_sp(ctx as *const _ as usize);

        ctx.init();
        // TODO: We should provide the thread a more rusty environment
        // to run the function safely.
        match entry {
            Entry::C(f) => ctx
                .set_return_address(run_simple_c as *const () as usize)
                .set_arg(0, unsafe { f as usize }),
            Entry::Closure(boxed) => {
                // FIXME: We need to make a new box to contain Box<dyn
                // FnOnce() + Send + 'static>, since *mut (dyn
                // FnOnce() + Send + 'static) is 64 bits in 32-bit
                // platform, aka, it's a fat pointer.
                let raw = Box::into_raw(Box::new(boxed));
                ctx.set_return_address(run_closure as *const () as usize)
                    .set_arg(0, raw as *mut Box<dyn FnOnce()> as usize)
            }
            Entry::Posix(f, arg) => ctx
                .set_return_address(run_posix as *const () as usize)
                .set_arg(0, unsafe { f as usize })
                .set_arg(1, unsafe { arg as usize }),
        };
        self
    }

    #[inline]
    pub fn priority(&self) -> ThreadPriority {
        self.priority
    }

    #[inline]
    pub fn disable_preempt(&self) -> bool {
        self.preempt_count.fetch_add(1, Ordering::Release) == 0
    }

    #[inline]
    pub fn enable_preempt(&self) -> bool {
        self.preempt_count.fetch_sub(1, Ordering::Release) == 1
    }

    #[inline]
    pub fn preempt_count(&self) -> Uint {
        self.preempt_count.load(Ordering::Acquire)
    }

    pub unsafe fn set_preempt_count(&self, val: Uint) -> &Self {
        self.preempt_count.store(val, Ordering::Release);
        self
    }

    #[cfg(thread_stats)]
    #[inline]
    pub fn increment_cycles(&self, cycles: u64) {
        self.stats.increment_cycles(cycles);
    }

    #[cfg(thread_stats)]
    #[inline]
    pub fn set_start_cycles(&self, cycles: u64) {
        self.stats.set_start_cycles(cycles);
    }

    #[cfg(thread_stats)]
    #[inline]
    pub fn start_cycles(&self) -> u64 {
        self.stats.start_cycles()
    }

    #[cfg(thread_stats)]
    #[inline]
    pub fn get_cycles(&self) -> u64 {
        self.stats.get_cycles()
    }

    #[cfg(event_flags)]
    #[inline]
    pub fn event_flags_mode(&self) -> EventFlagsMode {
        self.event_flags_mode
    }

    #[cfg(event_flags)]
    #[inline]
    pub fn event_flags_mask(&self) -> u32 {
        self.event_flags_mask
    }

    #[cfg(event_flags)]
    #[inline]
    pub fn set_event_flags_mode(&mut self, mode: EventFlagsMode) {
        self.event_flags_mode = mode;
    }

    #[cfg(event_flags)]
    #[inline]
    pub fn set_event_flags_mask(&mut self, mask: u32) {
        self.event_flags_mask = mask;
    }

    #[inline]
    pub fn set_alien_ptr(&mut self, ptr: NonNull<core::ffi::c_void>) {
        self.alien_ptr = Some(ptr);
    }

    #[inline]
    pub fn reset_alien_ptr(&mut self) -> &mut Self {
        self.alien_ptr = None;
        self
    }

    #[inline]
    pub fn get_alien_ptr(&self) -> Option<NonNull<core::ffi::c_void>> {
        self.alien_ptr
    }

    #[inline]
    pub fn origin_priority(&self) -> ThreadPriority {
        self.origin_priority
    }

    #[inline]
    pub fn set_origin_priority(&mut self, p: ThreadPriority) -> &mut Self {
        self.origin_priority = p;
        self
    }

    #[inline]
    pub fn pending_signals(&self) -> u32 {
        self.signal_context
            .as_ref()
            .map_or_else(|| 0, |c| {
                c.pending_signals.load(core::sync::atomic::Ordering::Acquire)
            })
    }

    #[inline]
    pub fn has_pending_signals(&self) -> bool {
        self.pending_signals() != 0
    }

    /// The set of signals this thread is blocking.
    #[inline]
    pub fn signal_mask(&self) -> &crate::signal::posix::ThreadSignalMask {
        &self.signal_mask
    }

    #[inline]
    pub fn clear_signal(&self, signum: i32) -> &Self {
        let Some(c) = &self.signal_context else {
            return self;
        };
        c.pending_signals
            .fetch_and(!(1 << signum), core::sync::atomic::Ordering::AcqRel);
        self
    }

    #[inline]
    pub fn clear_all_signals(&mut self) -> &Self {
        let Some(c) = &mut self.signal_context else {
            return self;
        };
        c.pending_signals
            .store(0, core::sync::atomic::Ordering::Release);
        self
    }

    #[inline]
    pub fn recover_priority(&mut self) -> &mut Self {
        self.priority = self.origin_priority;
        self
    }

    #[inline]
    pub fn promote_priority_to(&mut self, target_priority: ThreadPriority) -> bool {
        if target_priority >= self.priority {
            return false;
        }
        self.priority = target_priority;
        true
    }

    #[cfg(round_robin)]
    pub fn this_round_start_at(&self) -> Tick {
        self.rr.this_round_start_at.get()
    }

    #[cfg(round_robin)]
    pub fn set_this_round_start_at(&self, moment: Tick) -> &Self {
        self.rr.this_round_start_at.set(moment);
        self
    }

    #[cfg(round_robin)]
    pub fn remaining_time_slices(&self) -> Tick {
        self.rr.time_slices.get()
    }

    #[cfg(round_robin)]
    pub fn elapse_time_slices(&self, elapsed: Tick) -> Tick {
        let old = self.rr.time_slices.get();
        let diff = if elapsed.0 >= old.0 {
            Tick(0)
        } else {
            Tick(old.0 - elapsed.0)
        };
        self.rr.time_slices.set(diff);
        diff
    }

    #[cfg(round_robin)]
    pub fn refresh_time_slices(&self) -> Tick {
        let mut current = self.rr.time_slices.get();
        if current.0 != 0 {
            return current;
        }
        current = Tick(blueos_kconfig::CONFIG_ROBIN_SLICE as usize);
        self.rr.time_slices.set(current);
        current
    }
}

impl Drop for Thread {
    fn drop(&mut self) {
        debug_assert!(self.sched_node.is_detached());
        // The thread must have been detached from its owning process's
        // thread list before it is dropped; otherwise the process would
        // still hold a dangling strong reference to this thread.
        debug_assert!(self.process_node.is_detached());
    }
}

#[must_use]
pub(crate) struct PreemptGuard {
    t: ThreadNode,
    pub status: bool,
}

impl PreemptGuard {
    #[inline(always)]
    pub fn preemptable(&self) -> bool {
        self.status
    }
}

impl Drop for PreemptGuard {
    #[inline]
    fn drop(&mut self) {
        self.t.enable_preempt();
    }
}

impl !Send for Thread {}
unsafe impl Sync for Thread {}
