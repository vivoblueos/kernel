// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

#![no_std]
#![cfg_attr(test, feature(custom_test_frameworks))]
#![cfg_attr(test, test_runner(tests::adapter_test_runner))]
#![cfg_attr(test, reexport_test_harness_main = "adapter_test_main")]
#![cfg_attr(test, no_main)]

use alloc::boxed::Box;
use arch_crate as arch;
use blueos::{
    scheduler,
    scheduler::{wait_queue, wait_queue::WaitEntry, InsertToEnd},
    sync::SpinLock,
    thread::{Entry, Stack, ThreadNode, SUSPENDED},
    time::Tick,
    types::{Arc, ThreadPriority},
    with_iou,
};
use core::{
    cell::UnsafeCell,
    ffi::c_void,
    ptr::NonNull,
    sync::atomic::{AtomicBool, Ordering},
};
use esp_radio_rtos_driver::{
    queue::{CompatQueue, QueueHandle, QueuePtr},
    register_queue_implementation, register_scheduler_implementation,
    register_semaphore_implementation, register_timer_implementation,
    register_wait_queue_implementation,
    semaphore::{
        CompatSemaphore, SemaphoreHandle, SemaphoreImplementation, SemaphoreKind, SemaphorePtr,
    },
    timer::{CompatTimer, TimerHandle, TimerPtr},
    wait_queue::{WaitQueueHandle, WaitQueueImplementation, WaitQueuePtr},
    SchedulerImplementation, ThreadPtr,
};
extern crate alloc;

struct BkScheduler;

impl SchedulerImplementation for BkScheduler {
    fn initialized(&self) -> bool {
        scheduler::is_schedule_ready()
    }

    fn yield_task(&self) {
        scheduler::yield_me();
    }

    fn yield_task_from_isr(&self) {
        scheduler::yield_me_now_or_later();
    }

    fn max_task_priority(&self) -> u32 {
        blueos::config::MAX_THREAD_PRIORITY as u32
    }

    fn task_create(
        &self,
        _name: &str,
        task: extern "C" fn(*mut c_void),
        param: *mut c_void,
        priority: u32,
        _pin_to_core: Option<u32>,
        task_stack_size: usize,
    ) -> ThreadPtr {
        let entry = Entry::Posix(task, param);
        let stack = match Stack::from_size(task_stack_size) {
            Some(s) => s,
            None => return NonNull::dangling(),
        };
        // FreeRTOS priority is inverted relative to BlueOS: higher numeric value
        // means higher priority in FreeRTOS, but lower numeric value means higher
        // priority in BlueOS. Invert: blueos_prio = MAX - freertos_prio.
        let mut blueos_prio = blueos::config::MAX_THREAD_PRIORITY
            .saturating_sub(priority.min(blueos::config::MAX_THREAD_PRIORITY));
        if _name == "timer" {
            // The ESP timer service drives Wi-Fi scan dwell timeouts. If it stays
            // below the Wi-Fi task, a scan timer wake can leave the timer task READY
            // but unscheduled, stalling scan completion before association starts.
            blueos_prio = blueos_prio.min(1);
        }
        let thread = blueos::thread::Builder::new(entry)
            .set_stack(stack)
            .set_priority(blueos_prio as ThreadPriority)
            .start();
        // into_raw consumes the Arc without decrementing refcount,
        // so the pointer retains ownership of one reference until
        // schedule_task_deletion reclaims it via Arc::from_raw.
        let ptr = Arc::into_raw(thread) as *mut ();
        NonNull::new(ptr).unwrap()
    }

    fn current_task(&self) -> ThreadPtr {
        let thread = blueos::scheduler::current_thread();
        // as_ptr only borrows — the local Arc drops and refcount decrements,
        // but the thread is guaranteed alive (currently running).
        let ptr = Arc::as_ptr(&thread) as *mut ();
        NonNull::new(ptr).unwrap()
    }

    fn schedule_task_deletion(&self, task_handle: Option<ThreadPtr>) {
        let Some(handle) = task_handle else {
            // Delete self
            blueos::scheduler::retire_me();
            return;
        };
        let current = blueos::scheduler::current_thread_id();
        let target = handle.as_ptr() as usize;
        if current == target {
            blueos::scheduler::retire_me();
        } else {
            let mut thread: Arc<blueos::thread::Thread> =
                unsafe { Arc::from_raw(handle.as_ptr() as *const blueos::thread::Thread) };
            if thread.state() == blueos::thread::READY {
                blueos::scheduler::remove_from_ready_queue(&thread);
            }
            blueos::thread::GlobalQueueVisitor::remove(&mut thread);
        }
    }

    fn current_task_thread_semaphore(&self) -> SemaphorePtr {
        let thread = blueos::scheduler::current_thread();
        let mut w = thread.lock();
        if let Some(ptr) = w.get_alien_ptr() {
            NonNull::new(ptr.as_ptr() as *mut ()).unwrap()
        } else {
            let sem = SemaphoreHandle::new(SemaphoreKind::Counting { max: 1, initial: 0 }).leak();
            w.set_alien_ptr(NonNull::new(sem.as_ptr().cast()).unwrap());
            sem
        }
    }

    unsafe fn task_priority(&self, task: ThreadPtr) -> u32 {
        let thread = &*(task.as_ptr() as *const blueos::thread::Thread);
        let blueos_prio = thread.priority();
        // Invert: freertos_prio = MAX - blueos_prio
        blueos::config::MAX_THREAD_PRIORITY.saturating_sub(blueos_prio)
    }

    unsafe fn set_task_priority(&self, task: ThreadPtr, priority: u32) {
        let thread = &mut *(task.as_ptr() as *mut blueos::thread::Thread);
        let blueos_prio = blueos::config::MAX_THREAD_PRIORITY
            .saturating_sub(priority.min(blueos::config::MAX_THREAD_PRIORITY));
        thread.set_priority(blueos_prio as ThreadPriority);
    }

    fn usleep(&self, us: u32) {
        let _ = blueos::scheduler::suspend_me_for::<()>(Tick::from_micros(us as u64), None);
    }

    fn usleep_until(&self, target: u64) {
        let deadline = Tick::from_micros(target);
        let _ = blueos::scheduler::suspend_me_until::<()>(deadline, None);
    }

    fn now(&self) -> u64 {
        Tick::now().as_micros()
    }
}

/// Wrapper around a spinlocked kernel WaitQueue for use with the esp-radio driver.
///
/// The kernel's `WaitQueue` (`Ilist<WaitEntry, OffsetOfWait>`) is an intrusive linked list.
/// We wrap it in a `SpinLock` for thread safety, heap-allocate it, and expose it as an opaque
/// `WaitQueuePtr` to the esp-radio layer.
struct EspWaitQueue(wait_queue::WaitQueue);

impl WaitQueueImplementation for EspWaitQueue {
    fn create() -> WaitQueuePtr {
        let mut wq = Box::new(EspWaitQueue(wait_queue::WaitQueue::new()));
        wq.0.init();
        let ptr = Box::into_raw(wq);
        NonNull::new(ptr as *mut ()).unwrap()
    }

    unsafe fn delete(queue: WaitQueuePtr) {
        let ptr = queue.as_ptr() as *mut EspWaitQueue;
        let _ = Box::from_raw(ptr);
    }

    unsafe fn wait_until(queue: WaitQueuePtr, deadline_instant: Option<u64>) {
        let this = &mut *(queue.as_ptr() as *mut EspWaitQueue);
        let this_thread = scheduler::current_thread();
        let deadline = deadline_instant.map(Tick::from_micros).unwrap_or(Tick::MAX);
        let mut w = &mut this.0;
        with_iou!(|borrowed_wait_entry| {
            let mut wait_entry = WaitEntry::new(this_thread.clone());
            borrowed_wait_entry =
                wait_queue::insert(&mut w, &mut wait_entry, InsertToEnd::MODE).unwrap();
            let _ = scheduler::suspend_me_until::<()>(deadline, None);
            w = &mut this.0;
            borrowed_wait_entry = w.pop(borrowed_wait_entry).unwrap();
        });
    }

    unsafe fn notify(queue: WaitQueuePtr) {
        let this = &*(queue.as_ptr() as *const EspWaitQueue);
        let mut w = &this.0;
        let mut woke = false;
        for entry in w.iter() {
            let t = entry.thread.clone();
            woke = scheduler::queue_ready_thread(SUSPENDED, t).is_ok();
            break;
        }
        if woke {
            scheduler::yield_me_now_or_later();
        }
    }

    unsafe fn notify_from_isr(queue: WaitQueuePtr, mut higher_prio_task_waken: Option<&mut bool>) {
        let this = &mut *(queue.as_ptr() as *mut EspWaitQueue);
        let mut w = &mut this.0;
        for entry in w.iter() {
            let t = entry.thread.clone();
            if scheduler::queue_ready_thread(SUSPENDED, t).is_ok() {
                if let Some(hptw) = higher_prio_task_waken.as_mut() {
                    **hptw = true;
                }
            }
            break;
        }
    }
}

/// BkSemaphore: a semaphore implementation using short interrupt-disabled critical
/// sections instead of NonReentrantMutex. This avoids the "lock is not reentrant"
/// panic that occurs when CompatSemaphore's NonReentrantMutex is held across a
/// context switch inside EspWaitQueue::wait_until.
///
/// On single-core, saving and disabling local interrupts is sufficient for mutual
/// exclusion. Blocking waits must happen outside these critical sections so the
/// scheduler sees local interrupts enabled when suspending and resuming threads.
struct BkSemaphore {
    data: UnsafeCell<SemaphoreBkData>,
}

struct SemaphoreBkData {
    kind: SemaphoreKind,
    current: u32,
    max: u32,
    waiting: WaitQueuePtr,
    owner: usize,
    owner_thread: Option<ThreadNode>,
    owner_boosted: bool,
    recursion: u32,
}

unsafe impl Sync for BkSemaphore {}

impl BkSemaphore {
    fn new(kind: SemaphoreKind) -> Self {
        let (current, max) = match kind {
            SemaphoreKind::Counting { max, initial } => (initial, max),
            SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex => (1, 1),
        };
        BkSemaphore {
            data: UnsafeCell::new(SemaphoreBkData {
                kind,
                current,
                max,
                waiting: unsafe { EspWaitQueue::create() },
                owner: 0,
                owner_thread: None,
                owner_boosted: false,
                recursion: 0,
            }),
        }
    }

    /// Enter a short critical section, run `f`, then restore the full saved IRQ state.
    fn with_irq_safe<R>(&self, f: impl FnOnce(&mut SemaphoreBkData) -> R) -> R {
        let irq_level = arch::disable_local_irq_save();
        let r = f(unsafe { &mut *self.data.get() });
        arch::enable_local_irq_restore(irq_level);
        r
    }

    fn is_mutex_kind(kind: &SemaphoreKind) -> bool {
        matches!(kind, SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex)
    }

    fn promote_owner_for_waiter(owner_thread: &ThreadNode, waiter_thread: &ThreadNode) -> bool {
        let target_priority = waiter_thread.priority();
        let old_priority = owner_thread.priority();
        let mut promoted = false;

        if target_priority < old_priority {
            promoted = match scheduler::update_ready_thread_priority(owner_thread, target_priority)
            {
                Ok(()) => true,
                Err(_) => owner_thread.lock().promote_priority_to(target_priority),
            };
        }

        promoted
    }

    fn recover_owner_priority(owner_thread: &ThreadNode) -> bool {
        let old_priority = owner_thread.priority();
        let origin_priority = owner_thread.origin_priority();
        let mut recovered = false;

        if old_priority != origin_priority {
            recovered = match scheduler::update_ready_thread_priority(owner_thread, origin_priority)
            {
                Ok(()) => true,
                Err(_) => {
                    owner_thread.lock().recover_priority();
                    owner_thread.priority() != old_priority
                }
            };
        }

        recovered
    }
}

impl SemaphoreImplementation for BkSemaphore {
    fn create(kind: SemaphoreKind) -> SemaphorePtr {
        let sem = Box::new(Self::new(kind));
        NonNull::from(Box::leak(sem)).cast()
    }

    unsafe fn delete(semaphore: SemaphorePtr) {
        let sem = Box::from_raw(semaphore.cast::<Self>().as_ptr());
        // Delete the wait queue — no lock needed, nobody references this any more.
        EspWaitQueue::delete(sem.with_irq_safe(|d| d.waiting));
        drop(sem);
    }

    unsafe fn take(semaphore: SemaphorePtr, timeout_us: Option<u32>) -> bool {
        <Self as SemaphoreImplementation>::take_with_deadline(
            semaphore,
            timeout_us.map(|us| Tick::now().as_micros() + us as u64),
        )
    }

    unsafe fn take_with_deadline(semaphore: SemaphorePtr, _deadline_instant: Option<u64>) -> bool {
        let sem = &*semaphore.cast::<BkSemaphore>().as_ptr();
        loop {
            // Quick path: try to decrement current under a short critical section.
            // If semaphore is available, take it and return immediately.
            // If we need to block, the wait happens after with_irq_safe restores the
            // saved IRQ state.
            let current_thread = scheduler::current_thread();
            let current_owner = Arc::as_ptr(&current_thread) as usize;
            let (available, waiting, is_mutex, owner, owner_thread) = sem.with_irq_safe(|data| {
                let available = match &data.kind {
                    SemaphoreKind::RecursiveMutex if data.owner == current_owner => {
                        data.recursion = data.recursion.saturating_add(1);
                        true
                    }
                    SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex if data.current > 0 => {
                        data.current -= 1;
                        data.owner = current_owner;
                        data.owner_thread = Some(current_thread.clone());
                        data.owner_boosted = false;
                        data.recursion = 1;
                        true
                    }
                    _ if data.current > 0 => {
                        data.current -= 1;
                        true
                    }
                    _ => false,
                };
                (
                    available,
                    data.waiting,
                    Self::is_mutex_kind(&data.kind),
                    data.owner,
                    data.owner_thread.clone(),
                )
            });

            if available {
                return true;
            }

            if is_mutex && owner != 0 && owner != current_owner {
                if let Some(owner_thread) = owner_thread.as_ref() {
                    if Self::promote_owner_for_waiter(owner_thread, &current_thread) {
                        sem.with_irq_safe(|data| data.owner_boosted = true);
                    }
                }
            }

            // Semaphore not available — need to block.
            // wait_until handles insert + suspend + pop atomically (via with_iou!).
            // ESP Wi-Fi may call this while its upstream critical section has local
            // IRQ disabled. BlueOS cannot context-switch with local IRQ disabled, so
            // bridge the two contracts: save the caller's IRQ state, enable IRQ only
            // for the blocking wait, then restore the saved state after wait returns.
            if _deadline_instant.is_some_and(|d| Tick::now().as_micros() >= d) {
                return false;
            }
            let irq_level = arch::disable_local_irq_save();
            arch::enable_local_irq();
            // SAFETY: `waiting` pointer is immutable after new() — it is only
            // read here and in give().  `waiting` was already captured under the
            // guard above, so we use the local copy.
            unsafe {
                EspWaitQueue::wait_until(waiting, _deadline_instant);
            }
            arch::enable_local_irq_restore(irq_level);
        }
    }

    unsafe fn give(semaphore: SemaphorePtr) -> bool {
        let sem = &*semaphore.cast::<BkSemaphore>().as_ptr();
        let current_thread = scheduler::current_thread();
        let current_owner = Arc::as_ptr(&current_thread) as usize;
        let (ok, released, waiting, owner_thread, owner_boosted) = sem.with_irq_safe(|data| {
            let mut released_owner_thread = None;
            let mut released_owner_boosted = false;
            let (ok, released) = match &data.kind {
                SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex
                    if data.owner == current_owner =>
                {
                    if matches!(&data.kind, SemaphoreKind::RecursiveMutex) && data.recursion > 1 {
                        data.recursion -= 1;
                        (true, false)
                    } else {
                        data.recursion = 0;
                        data.owner = 0;
                        released_owner_thread = data.owner_thread.take();
                        released_owner_boosted = data.owner_boosted;
                        data.owner_boosted = false;
                        if data.current < data.max {
                            data.current += 1;
                        }
                        (true, true)
                    }
                }
                SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex => (false, false),
                _ if data.current < data.max => {
                    data.current += 1;
                    (true, true)
                }
                _ => (false, false),
            };
            (
                ok,
                released,
                data.waiting,
                released_owner_thread,
                released_owner_boosted,
            )
        });
        if released && owner_boosted {
            if let Some(owner_thread) = owner_thread.as_ref() {
                Self::recover_owner_priority(owner_thread);
            }
        }
        if released {
            unsafe { EspWaitQueue::notify(waiting) };
        }
        ok
    }

    unsafe fn try_give_from_isr(
        semaphore: SemaphorePtr,
        higher_prio_task_waken: Option<&mut bool>,
    ) -> bool {
        let sem = &*semaphore.cast::<BkSemaphore>().as_ptr();
        let (ok, waiting) = sem.with_irq_safe(|data| {
            let ok = match &data.kind {
                SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex => false,
                _ if data.current < data.max => {
                    data.current += 1;
                    true
                }
                _ => false,
            };
            (ok, data.waiting)
        });
        if ok {
            unsafe { EspWaitQueue::notify_from_isr(waiting, higher_prio_task_waken) };
        }
        ok
    }

    unsafe fn current_count(semaphore: SemaphorePtr) -> u32 {
        let sem = &*semaphore.cast::<BkSemaphore>().as_ptr();
        sem.with_irq_safe(|data| data.current)
    }

    unsafe fn try_take(semaphore: SemaphorePtr) -> bool {
        let sem = &*semaphore.cast::<BkSemaphore>().as_ptr();
        let current_thread = scheduler::current_thread();
        let current_owner = Arc::as_ptr(&current_thread) as usize;
        sem.with_irq_safe(|data| match &data.kind {
            SemaphoreKind::RecursiveMutex if data.owner == current_owner => {
                data.recursion = data.recursion.saturating_add(1);
                true
            }
            SemaphoreKind::Mutex | SemaphoreKind::RecursiveMutex if data.current > 0 => {
                data.current -= 1;
                data.owner = current_owner;
                data.owner_thread = Some(current_thread.clone());
                data.owner_boosted = false;
                data.recursion = 1;
                true
            }
            _ if data.current > 0 => {
                data.current -= 1;
                true
            }
            _ => false,
        })
    }

    unsafe fn try_take_from_isr(
        semaphore: SemaphorePtr,
        _higher_prio_task_waken: Option<&mut bool>,
    ) -> bool {
        <Self as SemaphoreImplementation>::try_take(semaphore)
    }
}

register_semaphore_implementation!(BkSemaphore);
register_queue_implementation!(CompatQueue);
register_timer_implementation!(CompatTimer);
register_wait_queue_implementation!(EspWaitQueue);
register_scheduler_implementation!(static SCHEDULER: BkScheduler = BkScheduler);

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::{
        allocator::{memory_info, KernelAllocator},
        arch, scheduler,
        thread::{Builder, Entry, Thread, ThreadNode},
    };
    use blueos_test_macro::test;

    #[global_allocator]
    static ALLOCATOR: KernelAllocator = KernelAllocator;

    #[used]
    #[link_section = ".bk_app_array"]
    static INIT_TEST: extern "C" fn() = init_test;

    #[inline(never)]
    pub fn adapter_test_runner(tests: &[&dyn Fn()]) {
        let t = scheduler::current_thread();
        semihosting::println!("Esp Radio Sys adapter unittest started");
        semihosting::println!("Running {} tests", tests.len());
        semihosting::println!(
            "Before test, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t),
            memory_info(),
            arch::current_sp(),
        );
        for test in tests {
            test();
        }
        semihosting::println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            memory_info(),
            arch::current_sp(),
        );
        semihosting::println!("Esp Radio Sys adapter unittest ended");

        #[cfg(coverage)]
        blueos::coverage::write_coverage_data();
    }

    extern "C" fn test_main() {
        adapter_test_main();
    }

    extern "C" fn init_test() {
        semihosting::println!("create test thread");
        let _t = Builder::new(Entry::C(test_main)).start();
    }

    #[test]
    fn scheduler_driver_api_exports_basic_state() {
        assert!(esp_radio_rtos_driver::initialized());
        assert!(esp_radio_rtos_driver::max_task_priority() > 0);
        assert_eq!(
            esp_radio_rtos_driver::current_task().as_ptr() as usize,
            Thread::id(&scheduler::current_thread())
        );

        let now = esp_radio_rtos_driver::now();
        esp_radio_rtos_driver::yield_task_from_isr();
        assert!(esp_radio_rtos_driver::now() >= now);
    }

    #[test]
    fn semaphore_handle_uses_registered_adapter() {
        let semaphore = SemaphoreHandle::new(SemaphoreKind::Counting { max: 2, initial: 1 });

        assert_eq!(semaphore.current_count(), 1);
        assert!(semaphore.try_take());
        assert_eq!(semaphore.current_count(), 0);
        assert!(!semaphore.try_take());

        assert!(semaphore.give());
        assert_eq!(semaphore.current_count(), 1);

        let mut higher_prio_task_waken = false;
        assert!(semaphore.try_take_from_isr(Some(&mut higher_prio_task_waken)));
        assert_eq!(semaphore.current_count(), 0);

        assert!(semaphore.try_give_from_isr(Some(&mut higher_prio_task_waken)));
        assert_eq!(semaphore.current_count(), 1);
    }

    #[test]
    fn queue_handle_preserves_send_receive_order() {
        let queue = QueueHandle::new(3, core::mem::size_of::<u32>());
        let first = 1u32;
        let second = 2u32;
        let front = 0u32;
        let mut out = u32::MAX;

        assert_eq!(queue.messages_waiting(), 0);
        unsafe {
            assert!(queue.send_to_back((&first as *const u32).cast(), Some(0)));
            assert!(queue.send_to_back((&second as *const u32).cast(), Some(0)));
            assert!(queue.send_to_front((&front as *const u32).cast(), Some(0)));
        }
        assert_eq!(queue.messages_waiting(), 3);

        unsafe {
            assert!(queue.receive((&mut out as *mut u32).cast(), Some(0)));
        }
        assert_eq!(out, front);

        unsafe {
            assert!(queue.receive((&mut out as *mut u32).cast(), Some(0)));
        }
        assert_eq!(out, first);

        let mut higher_prio_task_waken = false;
        unsafe {
            assert!(queue.try_receive_from_isr(
                (&mut out as *mut u32).cast(),
                Some(&mut higher_prio_task_waken)
            ));
        }
        assert_eq!(out, second);
        assert_eq!(queue.messages_waiting(), 0);
    }

    #[test]
    fn queue_handle_supports_isr_send_receive() {
        let queue = QueueHandle::new(1, core::mem::size_of::<u16>());
        let value = 0x1234u16;
        let mut out = 0u16;
        let mut higher_prio_task_waken = false;

        unsafe {
            assert!(queue.try_send_to_back_from_isr(
                (&value as *const u16).cast(),
                Some(&mut higher_prio_task_waken)
            ));
        }
        assert_eq!(queue.messages_waiting(), 1);

        unsafe {
            assert!(queue.try_receive_from_isr(
                (&mut out as *mut u16).cast(),
                Some(&mut higher_prio_task_waken)
            ));
        }
        assert_eq!(out, value);
        assert_eq!(queue.messages_waiting(), 0);
    }

    #[test]
    fn wait_queue_handle_notify_paths_are_registered() {
        let wait_queue = WaitQueueHandle::new();
        let mut higher_prio_task_waken = false;

        wait_queue.notify();
        wait_queue.notify_from_isr(Some(&mut higher_prio_task_waken));
        assert!(!higher_prio_task_waken);
    }

    unsafe extern "C" fn timer_test_callback(data: *mut c_void) {
        let fired = data.cast::<bool>();
        unsafe {
            *fired = true;
        }
    }

    #[test]
    fn timer_handle_arm_and_disarm_use_registered_adapter() {
        let mut fired = false;
        let timer =
            unsafe { TimerHandle::new(timer_test_callback, (&mut fired as *mut bool).cast()) };

        assert!(!timer.is_active());
        timer.arm(1_000_000, false);
        assert!(timer.is_active());
        assert!(!fired);

        timer.disarm();
        assert!(!timer.is_active());
    }

    #[panic_handler]
    fn oops(info: &core::panic::PanicInfo<'_>) -> ! {
        let _dig = blueos::support::DisableInterruptGuard::new();
        semihosting::println!("{}", info);
        semihosting::println!("Oops: {}", info.message());
        loop {}
    }
}
