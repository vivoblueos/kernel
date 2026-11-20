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
#![no_main]
extern crate librs;
extern crate rsrt;

use blueos::{arch, scheduler, support::DisableInterruptGuard, sync::SpinLock};
use core::sync::atomic::{AtomicUsize, Ordering};

static IRQ_LOCK: SpinLock<usize> = SpinLock::new(0);
static IRQ_RESULT: AtomicUsize = AtomicUsize::new(0);
const TEST_IRQ: arch::arm::irq::IrqNumber = arch::arm::irq::IrqNumber::new(0);

unsafe extern "C" fn test_irq() {
    IRQ_RESULT.store(
        if IRQ_LOCK.try_lock().is_some() { 1 } else { 2 },
        Ordering::Relaxed,
    );
}

fn pend_test_irq() {
    unsafe {
        core::ptr::write_volatile(0xe000e200 as *mut u32, 1);
        core::arch::asm!("dsb", "isb", options(nostack));
    }
}

fn irq_checks() {
    let irq = TEST_IRQ;
    unsafe {
        arch::arm::irq::register_raw_isr(irq, test_irq);
    }
    #[cfg(probe_high_irq)]
    arch::arm::irq::enable_irq_with_priority(irq, arch::arm::irq::Priority::High);
    #[cfg(not(probe_high_irq))]
    arch::arm::irq::enable_irq_with_priority(irq, arch::arm::irq::Priority::Normal);
    let g = IRQ_LOCK.lock();
    pend_test_irq();
    while IRQ_RESULT.load(Ordering::Relaxed) == 0 {
        core::hint::spin_loop();
    }
    assert_eq!(IRQ_RESULT.load(Ordering::Relaxed), 2);
    drop(g);
    IRQ_RESULT.store(0, Ordering::Relaxed);
    let g = IRQ_LOCK.irqsave_lock();
    pend_test_irq();
    assert_eq!(IRQ_RESULT.load(Ordering::Relaxed), 0);
    drop(g);
    while IRQ_RESULT.load(Ordering::Relaxed) == 0 {
        core::hint::spin_loop();
    }
    assert_eq!(IRQ_RESULT.load(Ordering::Relaxed), 1);
    arch::arm::irq::disable_irq(irq);
}

fn irq_wakes_semaphore_waiter() {
    use blueos::{sync::Semaphore, thread, time::Tick};
    use core::sync::atomic::AtomicBool;

    static SEMAPHORE: Semaphore = Semaphore::new();
    static RELEASE_RETURNED: AtomicBool = AtomicBool::new(false);

    unsafe extern "C" fn release_from_irq() {
        assert!(arch::arm::irq::is_irq_active(TEST_IRQ));
        SEMAPHORE.release();
        RELEASE_RETURNED.store(true, Ordering::Release);
    }

    assert!(SEMAPHORE.init(0));
    // SAFETY: irq_checks disabled this probe's IRQ before we replace its handler.
    unsafe { arch::arm::irq::register_raw_isr(TEST_IRQ, release_from_irq) };
    arch::arm::irq::enable_irq_with_priority(TEST_IRQ, arch::arm::irq::Priority::Normal);

    let waiter = scheduler::current_thread();
    thread::spawn(move || {
        while waiter.state() != thread::SUSPENDED {
            scheduler::suspend_me_for::<()>(Tick(1), None);
        }
        pend_test_irq();
    })
    .unwrap();

    assert!(
        SEMAPHORE.acquire_timeout::<scheduler::InsertToEnd>(Tick(100)),
        "IRQ did not wake the semaphore waiter before timeout"
    );
    assert!(RELEASE_RETURNED.load(Ordering::Acquire));
    assert_eq!(SEMAPHORE.count(), 0);
    arch::arm::irq::disable_irq(TEST_IRQ);
}

fn wait_checks() {
    use blueos::{
        sync::{atomic_wait, atomic_wake, mqueue::SendMode, MessageQueue, Semaphore},
        thread,
        time::Tick,
        types::Arc,
    };
    let sema = Arc::new(Semaphore::new());
    assert!(sema.init(0));
    let producer = sema.clone();
    thread::spawn(move || {
        scheduler::suspend_me_for::<()>(Tick(2), None);
        producer.release();
    })
    .unwrap();
    assert!(sema.acquire::<scheduler::InsertToEnd>(Tick(100)));
    let atom = Arc::new(AtomicUsize::new(0));
    let producer = atom.clone();
    thread::spawn(move || {
        scheduler::suspend_me_for::<()>(Tick(2), None);
        producer.store(1, Ordering::Release);
        atomic_wake(&producer, 1).unwrap();
    })
    .unwrap();
    atomic_wait(&atom, 0, Tick(100)).unwrap();
    assert_eq!(atom.load(Ordering::Acquire), 1);
    let queue = Arc::new(MessageQueue::new(4, 1, core::ptr::null_mut()).unwrap());
    assert!(queue.init());
    let producer = queue.clone();
    thread::spawn(move || {
        scheduler::suspend_me_for::<()>(Tick(2), None);
        producer
            .send(&[1, 2, 3, 4], 4, Tick(100), SendMode::Normal)
            .unwrap();
    })
    .unwrap();
    let mut buf = [0; 4];
    queue.recv(&mut buf, 4, Tick(100)).unwrap();
    assert_eq!(buf, [1, 2, 3, 4]);
    queue
        .send(&[5, 6, 7, 8], 4, Tick(100), SendMode::Normal)
        .unwrap();
    let consumer = queue.clone();
    thread::spawn(move || {
        scheduler::suspend_me_for::<()>(Tick(2), None);
        let mut buf = [0; 4];
        consumer.recv(&mut buf, 4, Tick(100)).unwrap();
        assert_eq!(buf, [5, 6, 7, 8]);
    })
    .unwrap();
    queue
        .send(&[9, 10, 11, 12], 4, Tick(100), SendMode::Normal)
        .unwrap();
    queue.recv(&mut buf, 4, Tick(100)).unwrap();
    assert_eq!(buf, [9, 10, 11, 12]);
}

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    librs::stdio::init();
    librs::pthread::register_my_posix_tcb();
    let lock = SpinLock::new(0usize);
    assert!(arch::local_irq_enabled());
    let mut w = lock.lock();
    assert!(arch::local_irq_enabled());
    assert!(lock.try_write().is_none());
    assert!(lock.try_read().is_none());
    *w = 42;
    #[cfg(probe_yield_in_lock)]
    scheduler::yield_me();
    scheduler::yield_me_now_or_later();
    assert_eq!(*w, 42);
    drop(w);
    let a = lock.read();
    let b = lock.read();
    assert_eq!(*a, 42);
    assert!(lock.try_write().is_none());
    drop(a);
    assert!(lock.try_write().is_none());
    drop(b);
    assert!(lock.try_write().is_some());
    let first = DisableInterruptGuard::new();
    let second = DisableInterruptGuard::new();
    assert!(!arch::local_irq_enabled());
    drop(first);
    assert!(!arch::local_irq_enabled());
    drop(second);
    assert!(arch::local_irq_enabled());
    let other = SpinLock::new(1);
    let a = lock.irqsave_lock();
    let b = other.irqsave_lock();
    assert!(lock.try_irqsave_read().is_none());
    assert!(lock.try_irqsave_lock().is_none());
    drop(a);
    assert!(!arch::local_irq_enabled());
    drop(b);
    assert!(arch::local_irq_enabled());
    irq_checks();
    irq_wakes_semaphore_waiter();
    wait_checks();
    // Stronger pre-existing masks survive entry and final restoration.
    unsafe {
        core::arch::asm!("msr basepri, {}", in(reg) 0x40u32, options(nostack));
    }
    let g = DisableInterruptGuard::new();
    let mask: u32;
    unsafe {
        core::arch::asm!("mrs {}, basepri", out(reg) mask, options(nostack));
    }
    assert_eq!(mask, 0x40);
    drop(g);
    unsafe {
        arch::enable_local_irq();
    }
    // A leaked plain guard must never restore access to the payload.
    let leaked = SpinLock::new(3);
    core::mem::forget(leaked.lock());
    assert!(leaked.try_write().is_none());
    assert!(leaked.try_read().is_none());
    // No scheduling is attempted after the deliberately leaked preemption lease.
    unsafe {
        libc::printf(c"LOCAL_LOCK_CONTRACT_PASS\n".as_ptr());
    }
    loop {
        core::hint::spin_loop();
    }
}
