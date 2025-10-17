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
    debug, scheduler,
    support::{Region, RegionalObjectBuilder, Storage},
    sync::{
        mutex::{MutexList, MutexListIterator},
        ISpinLock, Mutex, SpinLock, SpinLockGuard, SpinLockReadGuard, SpinLockWriteGuard,
    },
    thread::builder::GlobalQueue,
    time::timer::Timer,
    types::{
        impl_simple_intrusive_adapter, Arc, ArcCas, ArcList, AtomicUint, IlistHead, ThreadPriority,
        Uint, UniqueListHead,
    },
};
use alloc::boxed::Box;
use core::{
    alloc::Layout,
    ptr::NonNull,
    sync::atomic::{AtomicI32, AtomicU32, AtomicUsize, Ordering},
};

mod builder;
mod posix;
pub use builder::*;
use posix::*;

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

pub type Stack = Storage;

impl Stack {
    #[inline]
    pub fn top(&self) -> *mut u8 {
        unsafe { self.base().add(self.size()) }
    }

    #[inline]
    pub fn create(size: usize) -> Self {
        let layout = Layout::from_size_align(size, core::mem::align_of::<Context>()).unwrap();
        Self::from_layout(layout)
    }
}

impl_simple_intrusive_adapter!(OffsetOfSchedNode, Thread, sched_node);
impl_simple_intrusive_adapter!(OffsetOfGlobal, Thread, global);
impl_simple_intrusive_adapter!(OffsetOfLock, Thread, lock);

pub const CREATED: Uint = 0;
pub const READY: Uint = 1;
pub const RUNNING: Uint = 2;
pub const SUSPENDED: Uint = 3;
pub const RETIRED: Uint = 4;

// ThreadStats is protected by thread scheduler.
#[derive(Debug, Default)]
pub struct ThreadStats {
    start: u64,
    cycles: u64,
}

impl ThreadStats {
    pub const fn new() -> Self {
        Self {
            start: 0,
            cycles: 0,
        }
    }

    pub fn increment_cycles(&mut self, cycles: u64) {
        self.cycles += cycles.saturating_sub(self.start);
    }

    pub fn set_start_cycles(&mut self, start: u64) {
        self.start = start;
    }

    pub fn start_cycles(&self) -> u64 {
        self.start
    }

    pub fn get_cycles(&self) -> u64 {
        self.cycles
    }
}

pub(crate) type GlobalQueueListHead = UniqueListHead<Thread, OffsetOfGlobal, GlobalQueue>;

#[derive(Default)]
pub(crate) struct SignalContext {
    pending_signals: u32,
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
    pub timer: Option<Arc<Timer>>,
    // Cleanup function will be invoked when retiring.
    cleanup: Option<Entry>,
    kind: ThreadKind,
    // Thread owns Stack::Alloc. It calls dealloc when dropping its self.
    stack: Stack,
    saved_sp: usize,
    // This value may change at runtime.
    priority: ThreadPriority,
    // This is the static priority of this thread.
    origin_priority: ThreadPriority,
    state: AtomicUint,
    preempt_count: AtomicUint,
    #[cfg(robin_scheduler)]
    robin_count: AtomicI32,
    // FIXME: Using a rusty lock looks not flexible. Now we are using
    // a C-style intrusive lock. It's conventional to declare which
    // fields this lock is protecting. lock is protecting the
    // whole struct except those atomic fields.
    lock: ISpinLock<Thread, OffsetOfLock>,
    posix_compat: Option<PosixCompat>,
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
    // - Lock mutex's spinlcok
    // - Check mutex's pending queue
    acquired_mutexes: SpinLock<MutexList>,
    signal_context: Option<Box<SignalContext>>,
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
    pub fn validate_saved_sp(&self) -> bool {
        let sp = self.saved_sp;
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
            CREATED => "created",
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
    pub fn transfer_state(&self, from: Uint, to: Uint) -> bool {
        self.state
            .compare_exchange(from, to, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
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
    pub fn saved_sp_ptr(&self) -> *const u8 {
        &self.saved_sp as *const _ as *const u8
    }

    #[inline]
    pub fn saved_sp(&self) -> usize {
        self.saved_sp
    }

    #[inline]
    pub fn set_stack(&mut self, stack: Stack) -> &mut Self {
        self.stack = stack;
        self
    }

    const fn new(kind: ThreadKind) -> Self {
        Self::const_new(kind)
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
            .remove_if(|e| Arc::is(e, mu))
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

    const fn const_new(kind: ThreadKind) -> Self {
        Self {
            cleanup: None,
            stack: Stack::new(),
            state: AtomicUint::new(CREATED),
            lock: ISpinLock::new(),
            sched_node: IlistHead::<Thread, OffsetOfSchedNode>::new(),
            global: UniqueListHead::new(),
            saved_sp: 0,
            priority: 0,
            origin_priority: 0,
            preempt_count: AtomicUint::new(0),
            posix_compat: None,
            stats: ThreadStats::new(),
            timer: None,
            #[cfg(robin_scheduler)]
            robin_count: AtomicI32::new(0),
            kind,
            #[cfg(event_flags)]
            event_flags_mode: EventFlagsMode::empty(),
            #[cfg(event_flags)]
            event_flags_mask: 0,
            alien_ptr: None,
            pending_on_mutex: ArcCas::new(None),
            acquired_mutexes: SpinLock::new(MutexList::new()),
            signal_context: None,
        }
    }

    #[inline]
    pub fn id(me: &ThreadNode) -> usize {
        unsafe { ThreadNode::get_handle(me) as usize }
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
    pub(crate) fn reset_saved_sp(&mut self) -> &mut Self {
        self.saved_sp = self.stack.top() as usize;
        self
    }

    #[inline]
    pub(crate) fn set_saved_sp(&mut self, sp: usize) -> &mut Self {
        self.saved_sp = sp;
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
        let sig_ctx = self.get_or_create_signal_context();
        let old = sig_ctx.pending_signals;
        sig_ctx.pending_signals |= 1 << signum;
        // Return false if there is signum pending.
        (old & 1 << signum) == 0
    }

    pub fn register_once_signal_handler(&mut self, signum: i32, f: impl FnOnce() + 'static) {
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.once_action[signum as usize] = Some(Box::new(f));
    }

    pub fn take_signal_handler(&mut self, signum: i32) -> Option<Box<dyn FnOnce()>> {
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
        self.saved_sp = saved_sp;
    }

    pub(crate) fn signal_handler_sp(&mut self) -> usize {
        debug_assert_eq!(self.saved_sp % core::mem::align_of::<Context>(), 0);
        self.saved_sp - core::mem::size_of::<Context>()
    }

    pub(crate) fn init(&mut self, stack: Stack, entry: Entry) -> &mut Self {
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
        self.saved_sp = ctx as *const _ as usize;

        ctx.init();
        // TODO: We should provide the thread a more rusty environment
        // to run the function safely.
        match entry {
            Entry::C(f) => ctx
                .set_return_address(run_simple_c as usize)
                .set_arg(0, unsafe { f as usize }),
            Entry::Closure(boxed) => {
                // FIXME: We need to make a new box to contain Box<dyn
                // FnOnce() + Send + 'static>, since *mut (dyn
                // FnOnce() + Send + 'static) is 64 bits in 32-bit
                // platform, aka, it's a fat pointer.
                let raw = Box::into_raw(Box::new(boxed));
                ctx.set_return_address(run_closure as usize)
                    .set_arg(0, raw as *mut Box<dyn FnOnce()> as usize)
            }
            Entry::Posix(f, arg) => ctx
                .set_return_address(run_posix as usize)
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
        self.preempt_count.fetch_add(1, Ordering::Acquire) == 0
    }

    #[inline]
    pub fn enable_preempt(&self) -> bool {
        self.preempt_count.fetch_sub(1, Ordering::Acquire) == 1
    }

    #[inline]
    pub fn preempt_count(&self) -> Uint {
        self.preempt_count.load(Ordering::Relaxed)
    }

    #[cfg(robin_scheduler)]
    #[inline]
    pub fn round_robin(&self, tick: usize) -> i32 {
        self.robin_count.fetch_sub(tick as i32, Ordering::Relaxed)
    }

    #[cfg(robin_scheduler)]
    #[inline]
    pub fn reset_robin(&self) {
        self.robin_count
            .store(blueos_kconfig::ROBIN_SLICE as i32, Ordering::Relaxed);
    }

    #[inline]
    pub fn increment_cycles(&mut self, cycles: u64) {
        self.stats.increment_cycles(cycles);
    }

    #[inline]
    pub fn set_start_cycles(&mut self, cycles: u64) {
        self.stats.set_start_cycles(cycles);
    }

    #[inline]
    pub fn start_cycles(&self) -> u64 {
        self.stats.start_cycles()
    }

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
    pub fn pending_signals(&mut self) -> u32 {
        self.signal_context
            .as_ref()
            .map_or_else(|| 0, |c| c.pending_signals)
    }

    #[inline]
    pub fn has_pending_signals(&mut self) -> bool {
        self.pending_signals() != 0
    }

    #[inline]
    pub fn clear_signal(&mut self, signum: i32) -> &Self {
        let Some(c) = &mut self.signal_context else {
            return self;
        };
        c.pending_signals &= !(1 << signum);
        self
    }

    #[inline]
    pub fn clear_all_signals(&mut self) -> &Self {
        let Some(c) = &mut self.signal_context else {
            return self;
        };
        c.pending_signals = 0;
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
}

impl Drop for Thread {
    fn drop(&mut self) {
        assert!(self.sched_node.is_detached());
    }
}

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
