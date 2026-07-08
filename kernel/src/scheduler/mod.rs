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
    allocator,
    arch::{self, Context},
    signal,
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
    with_iou,
};
use alloc::boxed::Box;
use core::{
    intrinsics::unlikely,
    mem::MaybeUninit,
    ptr::NonNull,
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

// Per-CPU cache of the (PA, ASID, generation) triple currently installed in
// TTBR0_EL1.  All-zeros means no user process active (kernel thread running).
// SAFETY: Each CPU core only ever accesses its own slot via
// `arch::current_cpu_id()`.  No cross-CPU access, so `static mut` is
// data-race-free — same invariant as `RUNNING_THREADS` / `PER_CPU_TIMER`.
#[cfg(target_arch = "aarch64")]
#[derive(Copy, Clone)]
struct ProcCache {
    pa: usize,
    asid: u8,
    gen: u8,
}

#[cfg(target_arch = "aarch64")]
static mut PER_CPU_PROC_CACHE: [ProcCache; NUM_CORES] = [const {
    ProcCache {
        pa: 0,
        asid: 0,
        gen: 0,
    }
}; NUM_CORES];

#[cfg(target_arch = "aarch64")]
fn get_proc_cache() -> ProcCache {
    unsafe { PER_CPU_PROC_CACHE[arch::current_cpu_id()] }
}

#[cfg(target_arch = "aarch64")]
fn set_proc_cache(c: ProcCache) {
    unsafe {
        PER_CPU_PROC_CACHE[arch::current_cpu_id()] = c;
    }
}

/// Install the next thread's address space in `TTBR0_EL1`, with a per-CPU
/// `(PA, ASID, generation)` cache to skip redundant writes and TLB flushes.
///
/// Called from `switch_current_thread` on every context switch.  Extracted as
/// a standalone function so the §7 scheduler tests can exercise the cache
/// logic + TLBI issuance directly (via the `#[cfg(test)]` spy in
/// `arch::aarch64::asm`) without driving a full context switch.
///
/// - `next_proc == Some(p)`: if `(pa, asid, gen)` differs from the cache,
///   write `TTBR0_EL1 = (asid << 48) | pa`, issue `TLBI ASIDE1IS` for the old
///   ASID, DSB+ISB, and update the cache.  Otherwise (full hit) do nothing.
/// - `next_proc == None` (kernel thread): write `TTBR0_EL1 = 0`, issue
///   `TLBI VMALLE1IS` (Inner Shareable), DSB+ISB, reset the cache.  See
///   design D2.
#[cfg(target_arch = "aarch64")]
pub(crate) fn switch_address_space(next_proc: Option<NonNull<crate::process::Process>>) {
    use tock_registers::interfaces::Writeable;
    if let Some(proc) = next_proc {
        let proc_ref = unsafe { proc.as_ref() };
        let pa = proc_ref.address_space.root_pa();
        let asid = proc_ref.asid;
        let gen = proc_ref.asid_generation;
        // Cache hit requires all three keys to match: PA (same page
        // table), ASID (same TLB tag), and generation (same generation of
        // that ASID — a recycled ASID with a new generation must NOT hit
        // against a stale cache entry, design D4).
        let cache = get_proc_cache();
        if pa != cache.pa || asid != cache.asid || gen != cache.gen {
            let old_asid = cache.asid;
            crate::arch::aarch64::registers::ttbr0_el1::TTBR0_EL1
                .set((asid as u64) << 48 | pa as u64);
            // ASID 0 is never assigned to user processes; skip the no-op flush.
            if old_asid != 0 {
                crate::arch::aarch64::asm::tlbi_aside1is(old_asid);
            }
            crate::arch::aarch64::asm::dsb(crate::arch::aarch64::asm::DsbOptions::InnerShareable);
            crate::arch::aarch64::asm::isb();
            set_proc_cache(ProcCache { pa, asid, gen });
        }
    } else {
        // Switching to a kernel thread (next_proc == None): clear
        // TTBR0_EL1 and broadcast TLBI VMALLE1IS (Inner Shareable) to
        // purge the retiring user process's ASID+PA from every CPU's TLB.
        // VMALLE1IS (not ASIDE1IS) because a kernel thread has no ASID to
        // scope by; the stronger flush is acceptable since kernel-thread
        // switches are rare relative to same-process switches (design D2).
        crate::arch::aarch64::registers::ttbr0_el1::TTBR0_EL1.set(0);
        crate::arch::aarch64::asm::tlbi_vmalle1is();
        crate::arch::aarch64::asm::dsb(crate::arch::aarch64::asm::DsbOptions::InnerShareable);
        crate::arch::aarch64::asm::isb();
        set_proc_cache(ProcCache {
            pa: 0,
            asid: 0,
            gen: 0,
        });
    }
}

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

// Must use next's thread's stack or system stack to execute this function.
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
    #[cfg(round_robin)]
    {
        next.set_this_round_start_at(now);
        let time_slices = next.refresh_time_slices();
        let deadline = now.add(time_slices);
        set_current_timer(deadline);
    }
    #[cfg(thread_stats)]
    let cycles = time::current_clock_cycles();
    #[cfg(thread_stats)]
    next.set_start_cycles(cycles);
    let next_id = Thread::id(&next);
    let next_priority = next.priority();
    let next_saved_sp = spin_until_ready_to_run(&next);
    next.clear_saved_sp();
    // Reprogram per-thread MPU guard before restoring `next` context so the
    // upcoming PSP run is checked against the correct stack region.
    #[cfg(all(target_arch = "arm", use_mpu, mpu_stack_guard))]
    arch::mpu::update_thread_stack_guard(&next);
    let ok = next.transfer_state(thread::READY, thread::RUNNING);
    debug_assert_eq!(ok, Ok(()));
    #[cfg(target_arch = "aarch64")]
    let next_proc = next.process();
    let mut old = set_current_thread(next);
    // Switch TTBR0_EL1 when the next thread's address space differs from
    // the one currently installed on this CPU.  The PA/ASID/generation cache
    // avoids redundant TTBR0 writes and full TLB flushes for same-process
    // switches and kernel→same-user-process re-entries.
    #[cfg(target_arch = "aarch64")]
    switch_address_space(next_proc);
    #[cfg(thread_stats)]
    old.increment_cycles(cycles);
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
    #[cfg(round_robin)]
    {
        let start = old.this_round_start_at();
        let elapsed = now.since(start);
        old.elapse_time_slices(elapsed);
    }
    #[cfg(thread_stats)]
    old.increment_cycles(cycles);
    if old.state() == thread::RETIRED {
        GlobalQueueVisitor::remove(&mut old);
        if ThreadNode::strong_count(&old) != 1 {
            // TODO: Add warning log that there are still references to the old thread.
        }
        if let Some(entry) = old.lock().take_cleanup() {
            match entry {
                Entry::C(f) => f(),
                Entry::Closure(f) => f(),
                Entry::Posix(f, arg) => f(arg),
            }
        };
    }
    old.set_saved_sp(old_sp);
    next_saved_sp
}

// It's usually used in cortex-m's pendsv handler.
pub(crate) extern "C" fn relinquish_me_and_return_next_sp(old_sp: usize) -> usize {
    debug_assert_eq!(old_sp % core::mem::align_of::<Context>(), 0);
    debug_assert!(!arch::local_irq_enabled());
    debug_assert!(!crate::irq::is_in_irq());
    let old = current_thread_ref();
    debug_assert_eq!(old.preempt_count(), 0);
    let Some(next) = next_preferred_thread(old.priority()) else {
        #[cfg(debugging_scheduler)]
        crate::trace!("[TH:0x{:x}] keeps running", Thread::id(old));
        return old_sp;
    };
    debug_assert_eq!(next.state(), thread::READY);
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
    let retiring = current_thread_ref();
    #[cfg(procfs)]
    {
        let _ = crate::vfs::trace_thread_close(unsafe { Arc::clone_from(retiring) });
    }
    let next = next_ready_thread().map_or_else(idle::current_idle_thread, |v| v);
    debug_assert_eq!(next.state(), thread::READY);
    let mut hooks = ContextSwitchHookHolder::new(next);
    retiring.disable_preempt();
    let ok = retiring.transfer_state(thread::RUNNING, thread::RETIRED);
    debug_assert_eq!(ok, Ok(()));
    arch::switch_context_with_hook(&mut hooks as *mut _);
    unreachable!("Retired thread should not reach here")
}

fn inner_yield(next: ThreadNode) {
    let old = current_thread_ref();
    let mut hook_holder = ContextSwitchHookHolder::new(next);
    old.disable_preempt();
    if Thread::id(old) == Thread::id(idle::current_idle_thread_ref()) {
        let ok = old.transfer_state(thread::RUNNING, thread::READY);
        debug_assert_eq!(ok, Ok(()));
    } else {
        let ok = queue_ready_thread(thread::RUNNING, unsafe { Arc::clone_from(old) });
        debug_assert_eq!(ok, Ok(()));
    };
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
    // FIXME: Signal feature should be optional.
    {
        // FIXME: Do we need to change stack to handle signals?
        if !old.lock().has_pending_signals() {
            return;
        }
        signal::handle_signals();
    }
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

// FIXME: To support detaching a thread from a waitqueue or a sleepqueue on
// exception, we have to implement waking up the thread via signal. Currently,
// the timer is detached when the thread is re-scheduled, we have to implement
// detaching from a waitqueue uniformly.
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
        with_iou!(|iou| {
            let mut tm = Timer::new();
            tm.mode = TimerMode::Deadline(deadline);
            tm.callback = TimerCallback::Resched(Some(unsafe { Arc::clone_from(old) }), false);
            iou = timer::add_hard_timer(&mut tm).unwrap();
            arch::switch_context_with_hook(&mut hook_holder as *mut _);
            iou = timer::remove_hard_timer(iou).unwrap();
            reached_deadline = match tm.callback {
                TimerCallback::Resched(_, timeout) => timeout,
                _ => false,
            };
        });
    } else {
        arch::switch_context_with_hook(&mut hook_holder as *mut _);
    }
    debug_assert!(arch::local_irq_enabled());
    old.enable_preempt();
    // FIXME: Signal feature should be optional.
    {
        // FIXME: Do we need to change stack to handle signals?
        if !old.lock().has_pending_signals() {
            return reached_deadline;
        }
        signal::handle_signals();
    }
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
    #[cfg(not(round_robin))]
    return false;
    #[cfg(round_robin)]
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

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use super::*;
    use crate::{process::Process, types::Arc};
    use blueos_test_macro::test;
    use core::ptr::NonNull;
    use tock_registers::interfaces::Readable;

    /// Build an `Option<NonNull<Process>>` (the arg `switch_address_space`
    /// expects) from an `Arc<Process>`.
    fn proc_ref(p: &Arc<Process>) -> Option<NonNull<Process>> {
        NonNull::new(Arc::as_ptr(p) as *mut Process)
    }

    /// Read the currently-installed TTBR0_EL1 value.
    fn read_ttbr0() -> u64 {
        crate::arch::aarch64::registers::ttbr0_el1::TTBR0_EL1.get()
    }

    // 7.1: Switching to a kernel thread (next_proc == None) clears TTBR0_EL1
    // to 0 and issues TLBI VMALLE1IS (design D2).  We first install a user
    // process so TTBR0 is non-zero, then switch to None and assert the
    // cleanup.
    #[test]
    fn test_kernel_thread_switch_clears_ttbr0() {
        crate::arch::aarch64::asm::reset_tlbi_counters();
        // Install a user process so TTBR0_EL1 is non-zero and the cache holds
        // its (pa, asid, gen).
        let p = Process::try_new().expect("Process::try_new failed");
        switch_address_space(proc_ref(&p));
        assert_ne!(
            read_ttbr0(),
            0,
            "user process must install a non-zero TTBR0"
        );

        // Now switch to a kernel thread (None).
        let (aside_before, vmall_before) = crate::arch::aarch64::asm::read_tlbi_counters();
        switch_address_space(None);
        let (aside_after, vmall_after) = crate::arch::aarch64::asm::read_tlbi_counters();

        assert_eq!(read_ttbr0(), 0, "kernel-thread switch must clear TTBR0_EL1");
        assert_eq!(
            vmall_after - vmall_before,
            1,
            "kernel-thread switch must issue exactly one TLBI VMALLE1IS"
        );
        assert_eq!(
            aside_after - aside_before,
            0,
            "kernel-thread switch must NOT use ASIDE1IS (uses VMALLE1IS)"
        );
        // Caches reset to 0 (observable: a subsequent user-thread switch with
        // a different PA is a cache miss — covered by 7.3).
    }

    // 7.2: Switching between two threads of the SAME process is a full cache
    // hit — no TTBR0 write, no TLBI flush.
    #[test]
    fn test_same_process_switch_skips_tlb_flush() {
        let p = Process::try_new().expect("Process::try_new failed");
        // Prime the cache by installing the process once.
        switch_address_space(proc_ref(&p));
        let ttbr0_after_prime = read_ttbr0();

        // "Switch" to another thread of the same process: same (pa, asid, gen).
        crate::arch::aarch64::asm::reset_tlbi_counters();
        switch_address_space(proc_ref(&p));
        let (aside, vmall) = crate::arch::aarch64::asm::read_tlbi_counters();

        assert_eq!(
            read_ttbr0(),
            ttbr0_after_prime,
            "same-process switch must NOT rewrite TTBR0_EL1 (cache hit)"
        );
        assert_eq!(aside, 0, "same-process switch must NOT issue ASIDE1IS");
        assert_eq!(vmall, 0, "same-process switch must NOT issue VMALLE1IS");
    }

    // 7.3: Switching from process A to process B writes the new
    // (asid<<48)|pa into TTBR0_EL1 and issues TLBI ASIDE1IS for A's ASID.
    #[test]
    fn test_cross_process_switch_updates_ttbr0() {
        let a = Process::try_new().expect("Process::try_new failed");
        let b = Process::try_new().expect("Process::try_new failed");
        assert_ne!(a.asid, b.asid, "test precondition: distinct ASIDs");

        // Install A first.
        switch_address_space(proc_ref(&a));
        let ttbr0_a = read_ttbr0();
        assert_eq!(
            ttbr0_a,
            ((a.asid as u64) << 48) | (a.address_space.root_pa() as u64),
            "A's TTBR0 must encode A's asid+pa"
        );

        // Switch A → B.
        crate::arch::aarch64::asm::reset_tlbi_counters();
        switch_address_space(proc_ref(&b));
        let (aside, vmall) = crate::arch::aarch64::asm::read_tlbi_counters();

        assert_eq!(
            read_ttbr0(),
            ((b.asid as u64) << 48) | (b.address_space.root_pa() as u64),
            "B's TTBR0 must encode B's asid+pa after the switch"
        );
        assert_eq!(
            aside, 1,
            "cross-process switch must issue exactly one ASIDE1IS (for A's old ASID)"
        );
        assert_eq!(vmall, 0, "cross-process switch must NOT use VMALLE1IS");
    }

    // 7.4: Generation participates in the cache key.  A recycled ASID (same
    // asid, new generation) must NOT cache-hit against a stale cache entry.
    //
    // We simulate the recycle scenario directly: install process A (priming
    // the cache with A's PA/ASID/gen), then corrupt the cached generation to
    // a stale value.  Re-installing A — same PA, same ASID, but the cached
    // generation no longer matches — must be treated as a cache miss
    // (ASIDE1IS issued + TTBR0 rewritten).  This is exactly the situation
    // that arises after an ASID recycle: the new process has the same ASID
    // as the evicted one but a different generation.
    #[test]
    fn test_generation_in_cache_key() {
        let a = Process::try_new().expect("Process::try_new failed");

        // Prime the cache with A's real (pa, asid, gen).
        switch_address_space(proc_ref(&a));
        let cached_gen = get_proc_cache().gen;
        assert_eq!(
            cached_gen, a.asid_generation,
            "cache must hold A's generation after install"
        );

        // Simulate a stale cache entry: same PA and ASID, but a different
        // generation (as if the ASID was recycled to a new process with a
        // bumped generation while the cache still holds the old gen).
        let stale_gen = cached_gen.wrapping_add(1);
        assert_ne!(
            stale_gen, cached_gen,
            "test precondition: stale gen must differ"
        );
        let c = get_proc_cache();
        set_proc_cache(ProcCache {
            gen: stale_gen,
            ..c
        });

        // Re-install A.  Because the cached generation (stale_gen) != A's
        // real generation, this must be a cache MISS — TTBR0 rewritten and
        // ASIDE1IS issued.  If generation were NOT in the cache key, the
        // matching PA+ASID would falsely hit and skip the TLBI.
        crate::arch::aarch64::asm::reset_tlbi_counters();
        switch_address_space(proc_ref(&a));
        let (aside, vmall) = crate::arch::aarch64::asm::read_tlbi_counters();

        assert_eq!(
            aside, 1,
            "same PA+ASID but stale generation must be a cache MISS (ASIDE1IS issued)"
        );
        assert_eq!(vmall, 0, "must use ASIDE1IS, not VMALLE1IS");
        assert_eq!(
            get_proc_cache().gen,
            a.asid_generation,
            "cache must be updated to A's real generation after the miss"
        );

        // Now A → A with the correct cached generation: must be a hit.
        crate::arch::aarch64::asm::reset_tlbi_counters();
        switch_address_space(proc_ref(&a));
        let (aside_hit, _) = crate::arch::aarch64::asm::read_tlbi_counters();
        assert_eq!(
            aside_hit, 0,
            "A→A with matching generation must be a cache hit"
        );
    }
}
