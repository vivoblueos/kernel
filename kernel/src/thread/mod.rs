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
    config, debug, scheduler,
    support::{Region, RegionalObjectBuilder, Storage},
    sync::{ISpinLock, SpinLockGuard},
    thread::builder::GlobalQueue,
    time::timer::Timer,
    types::{
        impl_simple_intrusive_adapter, Arc, AtomicUint, IlistHead, ThreadPriority, Uint,
        UniqueListHead,
    },
};
use alloc::boxed::Box;
use core::{
    alloc::Layout,
    sync::atomic::{AtomicI32, AtomicUsize, Ordering},
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

#[derive(Debug, Copy, Clone, Default)]
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

    pub fn get_cycles(&self) -> u64 {
        self.cycles
    }
}

pub(crate) type GlobalQueueListHead = UniqueListHead<Thread, OffsetOfGlobal, GlobalQueue>;

#[derive(Default, Debug)]
pub struct Thread {
    global: GlobalQueueListHead,
    sched_node: IlistHead<Thread, OffsetOfSchedNode>,
    pub timer: Option<Arc<Timer>>,
    // Cleanup function will be invoked when retiring.
    cleanup: Option<Entry>,
    kind: ThreadKind,
    stack: Stack,
    saved_sp: usize,
    priority: ThreadPriority,
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

    pub(crate) fn init(&mut self, stack: Stack, entry: Entry) -> &mut Self {
        self.stack = stack;
        // TODO: Stack sanity check.
        self.saved_sp = self.stack.top() as usize - core::mem::size_of::<arch::Context>();
        let region = Region {
            base: self.saved_sp,
            size: core::mem::size_of::<arch::Context>(),
        };
        let mut builder = RegionalObjectBuilder::new(region);
        let ctx = unsafe {
            builder
                .zeroed_after_start::<arch::Context>()
                .unwrap_unchecked()
        };
        assert_eq!(ctx as *const _ as usize, self.saved_sp);
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
                    .set_arg(0, raw as *mut u8 as usize)
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
