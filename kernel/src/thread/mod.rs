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
    sync::atomic::{AtomicI32, AtomicU32, Ordering},
};

static NEXT_TID: AtomicU32 = AtomicU32::new(1);

mod builder;
pub use builder::*;

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

pub(crate) struct SignalContext {
    // Pending counts per signal number.
    // Index uses kernel numbering: slot N corresponds to signal N.
    // Slot 0 is unused.
    pending_counts: [u32; 32],
    // Whether this signal context is currently active (we're on signal stack).
    active: bool,
    // Will recover thread_context at recover_sp on exiting of signal handler.
    recover_sp: usize,
    thread_context: arch::Context,
    // Per-signal installed actions (sa_handler/sa_mask/sa_flags).
    sigactions: [KernelSigAction; 32],

    // Alternate signal stack description (empty ss_size == 0 means disabled).
    alt_stack: SigAltStack,

    // Per-signal queued siginfo (we don't support queueing multiple same-signals
    // yet; slot is overwritten by newer deliveries).
    pending_siginfo: [Option<SigInfo>; 32],
}

impl core::fmt::Debug for SignalContext {
    fn fmt(&self, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Ok(())
    }
}

impl Default for SignalContext {
    fn default() -> Self {
        Self {
            pending_counts: [0u32; 32],
            active: false,
            recover_sp: 0,
            thread_context: arch::Context::default(),
            sigactions: core::array::from_fn(|_| KernelSigAction::default()),
            alt_stack: SigAltStack::default(),
            pending_siginfo: core::array::from_fn(|_| None),
        }
    }
}

// Kernel-side lightweight siginfo (subset used by the kernel).
#[derive(Clone, Copy, Debug, Default)]
pub struct SigInfo {
    pub si_signo: i32,
    pub si_errno: i32,
    pub si_code: i32,
}

// Kernel representation of sigaction.
#[derive(Clone, Copy, Debug, Default)]
pub struct KernelSigAction {
    pub sa_handler: Option<extern "C" fn(i32)>,
    pub sa_flags: usize,
    pub sa_mask: libc::sigset_t,
}

// Kernel-side representation of sigaltstack (small subset).
#[derive(Clone, Copy, Debug)]
pub struct SigAltStack {
    pub ss_sp: *mut core::ffi::c_void,
    pub ss_flags: i32,
    pub ss_size: usize,
}

impl Default for SigAltStack {
    fn default() -> Self {
        Self {
            ss_sp: core::ptr::null_mut(),
            ss_flags: 0,
            ss_size: 0,
        }
    }
}

#[derive(Debug)]
pub struct Thread {
    tid: u32,
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
    // Current signal mask (POSIX numbering: signal N is bit N-1).
    blocked_mask: u32,
    // Saved mask used by syscalls that temporarily replace the mask (e.g. sigsuspend).
    saved_mask: u32,
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
    pub fn transfer_state(&self, from: Uint, to: Uint) -> bool {
        self.state
            .compare_exchange(from, to, Ordering::AcqRel, Ordering::Acquire)
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
            .remove_if(|e| Arc::as_ptr(mu) == e as *const _)
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

    const fn new(kind: ThreadKind) -> Self {
        Self {
            tid: 0,
            cleanup: None,
            stack: Stack::new(),
            state: AtomicUint::new(IDLE),
            lock: ISpinLock::new(),
            sched_node: IlistHead::<Thread, OffsetOfSchedNode>::new(),
            global: UniqueListHead::new(),
            saved_sp: 0,
            priority: 0,
            origin_priority: 0,
            preempt_count: AtomicUint::new(0),
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
            blocked_mask: 0,
            saved_mask: 0,
        }
    }

    #[inline]
    pub fn id(me: &Self) -> usize {
        me as *const Self as usize
    }

    #[inline]
    pub fn tid(me: &Self) -> u32 {
        me.tid
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

    pub fn kill(&mut self, signum: i32) -> bool {
        let sig_ctx = self.get_or_create_signal_context();
        if signum <= 0 || signum >= 32 {
            return false;
        }
        let idx = signum as usize;
        let old = sig_ctx.pending_counts[idx];
        sig_ctx.pending_counts[idx] = old.saturating_add(1);
        // Return false if there is signum already pending.
        old == 0
    }

    pub fn install_signal_handler(
        &mut self,
        signum: i32,
        handler: extern "C" fn(i32),
    ) -> &mut Self {
        let sa = KernelSigAction {
            sa_handler: Some(handler),
            sa_flags: 0,
            sa_mask: 0,
        };
        self.set_sigaction(signum, sa)
    }

    // Set per-signal action (kernel representation). signum must be 0..32.
    pub fn set_sigaction(&mut self, signum: i32, sa: KernelSigAction) -> &mut Self {
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.sigactions[signum as usize] = sa;
        self
    }

    // Get per-signal action.
    pub fn get_sigaction(&self, signum: i32) -> KernelSigAction {
        self.signal_context
            .as_ref()
            .map_or_else(KernelSigAction::default, |c| c.sigactions[signum as usize])
    }

    // Push a siginfo for `signum` into per-thread slot and mark it pending.
    pub fn push_siginfo(&mut self, signum: i32, info: SigInfo) -> &mut Self {
        let sig_ctx = self.get_or_create_signal_context();
        if signum > 0 && signum < 32 {
            let idx = signum as usize;
            sig_ctx.pending_siginfo[idx] = Some(info);
            sig_ctx.pending_counts[idx] = sig_ctx.pending_counts[idx].saturating_add(1);
        }
        self
    }

    // Take pending siginfo for `signum`.
    pub fn take_siginfo(&mut self, signum: i32) -> Option<SigInfo> {
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.pending_siginfo[signum as usize].take()
    }

    // Set or query alternate signal stack.
    pub fn set_sigaltstack(&mut self, ss: SigAltStack) -> &mut Self {
        let sig_ctx = self.get_or_create_signal_context();
        sig_ctx.alt_stack = ss;
        self
    }

    pub fn get_sigaltstack(&self) -> SigAltStack {
        self.signal_context
            .as_ref()
            .map_or_else(SigAltStack::default, |c| c.alt_stack)
    }

    pub fn is_signal_blocked(&self, signum: i32) -> bool {
        if signum <= 0 || signum >= 32 {
            return false;
        }
        // We only support standard signals 1..31 here; treat sigset_t as a
        // bitset and check the (signum-1) bit.
        let bit: u32 = 1u32 << ((signum - 1) as u32);
        (self.blocked_mask & bit) != 0
    }

    // Returns the current signal mask (POSIX numbering: bit (signum-1)).
    pub fn signal_mask(&self) -> u32 {
        self.blocked_mask
    }

    // Replace the current signal mask.
    pub fn set_signal_mask(&mut self, new_mask: u32) {
        self.blocked_mask = new_mask;
    }

    // Save the current signal mask for later restoration (used by sigsuspend-like syscalls).
    pub fn save_signal_mask(&mut self) {
        self.saved_mask = self.blocked_mask;
    }

    // Restore the previously saved signal mask.
    pub fn restore_saved_signal_mask(&mut self) {
        self.blocked_mask = self.saved_mask;
    }

    // Returns the current pending signal bitmap using *kernel numbering* (bit = 1 << signum).
    pub fn pending_signals_bitmap(&self) -> u32 {
        self.signal_context.as_ref().map_or(0, |c| {
            let mut bits: u32 = 0;
            for signum in 1..32 {
                if c.pending_counts[signum] != 0 {
                    bits |= 1u32 << (signum as u32);
                }
            }
            bits
        })
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

    // Compute the stack pointer to use for signal delivery.
    //
    // If SA_ONSTACK is requested for the delivered signal and an alternate
    // signal stack is configured (and not disabled), we deliver on that stack.
    // Otherwise we fall back to the thread's normal stack (the legacy behavior).
    pub(crate) fn signal_delivery_sp(&mut self, signum: i32) -> usize {
        let sa = self.get_sigaction(signum);
        // Only use altstack when requested.
        let want_onstack = (sa.sa_flags as i32) & libc::SA_ONSTACK != 0;
        if want_onstack {
            let ss = self.get_sigaltstack();
            if !ss.ss_sp.is_null() && ss.ss_size != 0 && (ss.ss_flags & libc::SS_DISABLE) == 0 {
                // Place the signal handler context at the top of the alt stack.
                // Keep it aligned like the normal path.
                let mut sp = (ss.ss_sp as usize).saturating_add(ss.ss_size);
                sp &= !(core::mem::align_of::<Context>() - 1);
                return sp.saturating_sub(core::mem::size_of::<Context>());
            }
        }
        self.signal_handler_sp()
    }

    pub(crate) fn init(&mut self, stack: Stack, entry: Entry) -> &mut Self {
        if self.tid == 0 {
            self.tid = NEXT_TID.fetch_add(1, Ordering::Relaxed);
        }
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
    pub fn round_robin(&self, ticks: usize) -> i32 {
        self.robin_count.fetch_sub(ticks as i32, Ordering::Relaxed)
    }

    #[cfg(robin_scheduler)]
    #[inline]
    pub fn reset_robin(&self) {
        self.robin_count
            .store(blueos_kconfig::CONFIG_ROBIN_SLICE as i32, Ordering::Relaxed);
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
        self.signal_context.as_ref().map_or(0, |c| {
            let mut bits: u32 = 0;
            for signum in 1..32 {
                if c.pending_counts[signum] != 0 {
                    bits |= 1u32 << (signum as u32);
                }
            }
            bits
        })
    }

    #[inline]
    pub fn has_pending_signals(&mut self) -> bool {
        let pending = self.pending_signals();
        // `blocked` uses POSIX numbering (signal N is bit (N-1)).
        // `pending_signals` uses kernel numbering (signal N is bit N).
        // For now we only consider signals 1..31 (NSIG=32) and treat 0 as unused.
        for signum in 1..32 {
            if pending & (1 << signum) == 0 {
                continue;
            }
            let bit: u32 = 1u32 << ((signum - 1) as u32);
            let is_blocked = (self.blocked_mask & bit) != 0;
            if !is_blocked {
                return true;
            }
        }
        false
    }

    #[inline]
    pub fn clear_signal(&mut self, signum: i32) -> &Self {
        let Some(c) = &mut self.signal_context else {
            return self;
        };
        if signum <= 0 || signum >= 32 {
            return self;
        }
        let idx = signum as usize;
        if c.pending_counts[idx] != 0 {
            c.pending_counts[idx] -= 1;
            if c.pending_counts[idx] == 0 {
                c.pending_siginfo[idx] = None;
            }
        }
        self
    }

    #[inline]
    pub fn clear_all_signals(&mut self) -> &Self {
        let Some(c) = &mut self.signal_context else {
            return self;
        };
        c.pending_counts = [0u32; 32];
        c.pending_siginfo = core::array::from_fn(|_| None);
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
        debug_assert!(self.sched_node.is_detached());
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
