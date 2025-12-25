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

#![no_std]
#![allow(internal_features)]
#![allow(incomplete_features)]
#![allow(clippy::crate_in_macro_def)]
#![feature(alloc_error_handler)]
#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(associated_type_defaults)]
#![feature(async_closure)]
#![feature(box_as_ptr)]
#![feature(c_size_t)]
#![feature(c_variadic)]
#![feature(const_trait_impl)]
#![feature(core_intrinsics)]
#![feature(coverage_attribute)]
#![feature(fn_align)]
#![feature(inherent_associated_types)]
#![feature(lazy_get)]
#![feature(link_llvm_intrinsics)]
#![feature(linkage)]
#![feature(macro_metavar_expr)]
#![feature(map_try_insert)]
#![feature(naked_functions)]
#![feature(negative_impls)]
#![feature(new_zeroed_alloc)]
#![feature(noop_waker)]
#![feature(pointer_is_aligned_to)]
#![feature(trait_upcasting)]
#![feature(trivial_bounds)]
// Attributes applied when we're testing the kernel.
#![cfg_attr(test, no_main)]
#![cfg_attr(test, feature(custom_test_frameworks))]
#![cfg_attr(test, test_runner(tests::kernel_unittest_runner))]
#![cfg_attr(test, reexport_test_harness_main = "run_kernel_unittests")]

extern crate alloc;

pub mod allocator;
pub mod arch;
#[cfg(kernel_async)]
pub mod asynk;
pub mod boards;
#[cfg(use_kernel_boot)]
pub(crate) mod boot;
pub mod config;
pub mod console;
#[cfg(coverage)]
pub mod coverage;
pub(crate) mod devices;
pub(crate) mod drivers;
pub mod error;
pub mod ffi;
pub mod irq;
pub mod logger;
#[cfg(enable_net)]
pub mod net;
pub mod scheduler;
pub mod support;
pub mod sync;
pub mod syscall_handlers;
pub mod thread;
pub mod time;
pub mod types;
#[cfg(enable_vfs)]
pub mod vfs;

pub use syscall_handlers as syscalls;
pub(crate) mod signal;

#[macro_export]
macro_rules! debug {
    ($($tt:tt)*) => {{}};
}

pub(crate) static TRACER: spin::Mutex<()> = spin::Mutex::new(());

#[macro_export]
macro_rules! trace {
    ($($tt:tt)*) => {{
        let dig = $crate::support::DisableInterruptGuard::new();
        let l = $crate::TRACER.lock();
        #[cfg(target_pointer_width="32")]
        semihosting::eprint!("[C:{:02} SP:0x{:08x}] ",
                             $crate::arch::current_cpu_id(),
                             $crate::arch::current_sp());
        #[cfg(target_pointer_width="64")]
        semihosting::eprint!("[C:{:02} SP:0x{:016x}] ",
                             $crate::arch::current_cpu_id(),
                             $crate::arch::current_sp());
        semihosting::eprintln!($($tt)*);
        drop(l);
        drop(dig);
    }};
}

#[cfg(test)]
mod tests {
    extern crate alloc;
    use super::*;
    use crate::{
        allocator, allocator::KernelAllocator, config, support::DisableInterruptGuard, sync,
        sync::ConstBarrier, time::WAITING_FOREVER, types::Arc,
    };
    use alloc::vec::Vec;
    use blueos_header::syscalls::NR::Nop;
    use blueos_test_macro::test;
    use core::{
        mem::MaybeUninit,
        panic::PanicInfo,
        ptr,
        sync::atomic::{AtomicUsize, Ordering},
    };
    #[cfg(use_defmt)]
    use defmt_rtt as _;
    use spin::Lazy;
    use thread::{Entry, SystemThreadStorage, Thread, ThreadKind, ThreadNode};

    #[used]
    #[link_section = ".bk_app_array"]
    static INIT_TEST: extern "C" fn() = init_test;

    extern "C" fn test_main() {
        run_kernel_unittests();
    }

    #[cfg(target_pointer_width = "32")]
    const K: usize = 1;

    #[cfg(all(debug_assertions, target_pointer_width = "64"))]
    pub const K: usize = 1;
    #[cfg(all(not(debug_assertions), target_pointer_width = "64"))]
    pub const K: usize = 64;

    const NUM_CORES: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;
    static mut TEST_THREAD_STORAGES: [SystemThreadStorage; NUM_CORES * K] =
        [const { SystemThreadStorage::new(ThreadKind::Normal) }; NUM_CORES * K];
    static mut TEST_THREADS: [MaybeUninit<ThreadNode>; NUM_CORES * K] =
        [const { MaybeUninit::zeroed() }; NUM_CORES * K];

    static mut MAIN_THREAD_STORAGE: SystemThreadStorage =
        SystemThreadStorage::new(ThreadKind::Normal);
    static mut MAIN_THREAD: MaybeUninit<ThreadNode> = MaybeUninit::zeroed();

    fn reset_and_queue_test_thread(
        i: usize,
        entry: extern "C" fn(),
        cleanup: Option<extern "C" fn()>,
    ) {
        unsafe {
            let t = TEST_THREADS[i].assume_init_ref();
            let mut w = t.lock();
            let stack = &mut TEST_THREAD_STORAGES[i].stack;
            let stack = thread::Stack::from_raw(stack.rep.as_mut_ptr(), stack.rep.len());
            w.init(stack, thread::Entry::C(entry));
            if let Some(cleanup) = cleanup {
                w.set_cleanup(Entry::C(cleanup));
            };
            let ok = scheduler::queue_ready_thread(w.state(), t.clone());
            assert!(ok);
        }
    }

    fn reset_and_queue_test_threads(entry: extern "C" fn(), cleanup: Option<extern "C" fn()>) {
        unsafe {
            for i in 0..TEST_THREADS.len() {
                reset_and_queue_test_thread(i, entry, cleanup);
            }
        }
    }

    fn init_test_thread(i: usize) {
        let t = thread::build_static_thread(
            unsafe { &mut TEST_THREADS[i] },
            unsafe { &mut TEST_THREAD_STORAGES[i] },
            config::MAX_THREAD_PRIORITY / 2,
            thread::CREATED,
            Entry::C(test_main),
            ThreadKind::Normal,
        );
    }

    extern "C" fn init_test() {
        let l = unsafe { TEST_THREADS.len() };
        for i in 0..l {
            init_test_thread(i);
        }
        let t = thread::build_static_thread(
            unsafe { &mut MAIN_THREAD },
            unsafe { &mut MAIN_THREAD_STORAGE },
            config::MAX_THREAD_PRIORITY / 2,
            thread::CREATED,
            Entry::C(test_main),
            ThreadKind::Normal,
        );
        let ok = scheduler::queue_ready_thread(thread::CREATED, t.clone());
        assert!(ok);
    }

    #[cfg(target_pointer_width = "64")]
    const EMBALLOC_SIZE: usize = 8 << 20;
    #[cfg(target_pointer_width = "32")]
    const EMBALLOC_SIZE: usize = 2 << 20;

    #[global_allocator]
    static ALLOCATOR: KernelAllocator = KernelAllocator;
    // Emballoc is for correctness reference.
    //static ALLOCATOR: emballoc::Allocator<{ EMBALLOC_SIZE }> = emballoc::Allocator::new();

    #[panic_handler]
    fn oops(info: &PanicInfo) -> ! {
        let _guard = DisableInterruptGuard::new();
        #[cfg(not(use_defmt))]
        {
            semihosting::println!("{}", info);
            semihosting::println!("Oops: {}", info.message());
        }

        #[cfg(use_defmt)]
        {
            defmt::error!("{}", defmt::Display2Format(info));
            defmt::error!("Oops: {}", defmt::Display2Format(&info.message()));
        }
        loop {}
    }

    #[test]
    fn test_spinlock() {
        let lock = sync::spinlock::SpinLock::new(0);
        let mut w = lock.irqsave_lock();
        *w = 1;
        drop(w);

        assert!(scheduler::current_thread().validate_sp());
        scheduler::yield_me_now_or_later();
        assert!(scheduler::current_thread().validate_sp());

        let r = lock.irqsave_lock();
        assert_eq!(*r, 1);
    }

    #[test]
    fn test_spinlock_loop() {
        let lock = sync::spinlock::SpinLock::new(0);
        loop {
            let mut w = lock.irqsave_lock();
            *w += 1;
            drop(w);

            scheduler::yield_me_now_or_later();

            let r = lock.irqsave_lock();
            if *r == 100 {
                break;
            }
        }
    }

    #[cfg(cortex_m)]
    #[test]
    fn test_sys_tick() {
        let tick = time::TickTime::now().as_ticks();
        assert!(scheduler::current_thread().validate_sp());
        scheduler::suspend_me_for(10);
        assert!(scheduler::current_thread().validate_sp());
        let tick2 = time::TickTime::now().as_ticks();
        assert!(tick2 - tick >= 10);
        assert!(tick2 - tick <= 11);
    }

    #[test]
    fn test_local_irq() {
        assert!(arch::local_irq_enabled());
    }

    #[test]
    fn stress_trap() {
        #[cfg(target_pointer_width = "32")]
        let n = 16;
        #[cfg(target_pointer_width = "64")]
        let n = 256;
        for _i in 0..n {
            #[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
            unsafe {
                core::arch::asm!(
                    "ecall",
                    in("a7") Nop as usize,
                    inlateout("a0") 0 => _,
                    options(nostack),
                );
            };
        }
    }

    #[derive(Default)]
    struct CleanupCounter {
        counter: AtomicUsize,
    }

    impl CleanupCounter {
        pub const fn new() -> Self {
            Self {
                counter: AtomicUsize::new(0),
            }
        }
        pub fn spin_until_eq(&self, n: usize) {
            while self.counter.load(Ordering::Relaxed) != n {
                core::hint::spin_loop();
            }
        }
        pub fn increment(&self) {
            self.counter.fetch_add(1, Ordering::Relaxed);
        }
    }

    static SEMA_CLEANUP_COUNTER: CleanupCounter = CleanupCounter::new();
    static mut SEMA_COUNTER: usize = 0usize;
    static SEMA: sync::semaphore::Semaphore = sync::semaphore::Semaphore::new();

    extern "C" fn test_semaphore() {
        SEMA.acquire_notimeout::<scheduler::InsertToEnd>();
        let n = unsafe { SEMA_COUNTER };
        unsafe { SEMA_COUNTER += 1 };
        SEMA.release();
    }

    extern "C" fn test_semaphore_cleanup() {
        SEMA_CLEANUP_COUNTER.increment();
    }

    #[test]
    fn stress_semaphore() {
        SEMA.init(1);
        reset_and_queue_test_threads(test_semaphore, Some(test_semaphore_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        loop {
            SEMA.acquire_notimeout::<scheduler::InsertToEnd>();
            let n = unsafe { SEMA_COUNTER };
            if n == l {
                SEMA.release();
                break;
            }
            SEMA.release();
            scheduler::yield_me();
        }
        SEMA_CLEANUP_COUNTER.spin_until_eq(l);
    }

    static ATOMIC_WAIT_CLEANUP: CleanupCounter = CleanupCounter::new();
    static TEST_ATOMIC_WAIT: AtomicUsize = AtomicUsize::new(0);

    extern "C" fn test_atomic_wait_cleanup() {
        ATOMIC_WAIT_CLEANUP.increment();
    }

    extern "C" fn test_atomic_wait() {
        TEST_ATOMIC_WAIT.fetch_add(1, Ordering::Release);
        sync::atomic_wait::atomic_wake(&TEST_ATOMIC_WAIT, 1);
    }

    #[test]
    fn stress_atomic_wait() {
        reset_and_queue_test_threads(test_atomic_wait, Some(test_atomic_wait_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        loop {
            let n = TEST_ATOMIC_WAIT.load(Ordering::Acquire);
            if n == l {
                break;
            }
            sync::atomic_wait::atomic_wait(&TEST_ATOMIC_WAIT, n, None);
        }
        ATOMIC_WAIT_CLEANUP.spin_until_eq(l);
    }

    static MUTEX_CLEANUP: CleanupCounter = CleanupCounter::new();
    static_arc! {
        MUTEX(sync::mutex::Mutex, sync::mutex::Mutex::new()),
    }
    static mut MUTEX_COUNTER: usize = 0usize;

    extern "C" fn test_mutex() {
        MUTEX.pend_for(WAITING_FOREVER);
        unsafe { MUTEX_COUNTER += 1 };
        MUTEX.post();
    }

    extern "C" fn test_mutex_cleanup() {
        MUTEX_CLEANUP.increment();
    }

    #[test]
    fn stress_mutex() {
        MUTEX.init();
        reset_and_queue_test_threads(test_mutex, Some(test_mutex_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        loop {
            MUTEX.pend_for(WAITING_FOREVER);
            let n = unsafe { MUTEX_COUNTER };
            if n == l {
                MUTEX.post();
                break;
            }
            MUTEX.post();
            scheduler::yield_me();
        }
        MUTEX_CLEANUP.spin_until_eq(l);
    }

    static MQUEUE: Lazy<Arc<sync::mqueue::MessageQueue>> =
        Lazy::new(|| Arc::new(sync::mqueue::MessageQueue::new(4, 2, ptr::null_mut())));
    static TEST_SEND_CNT: AtomicUsize = AtomicUsize::new(0);

    extern "C" fn test_mqueue() {
        let buffer = [1u8; 4];
        let result = MQUEUE.send(&buffer, 4, 512, sync::mqueue::SendMode::Normal);
        assert!(result.is_ok());
    }

    extern "C" fn test_mqueue_cleanup() {
        TEST_SEND_CNT.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn stress_mqueue() {
        MQUEUE.init();
        reset_and_queue_test_threads(test_mqueue, Some(test_mqueue_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        let mut recv_cnt = 0;
        let mut buffer = [0u8; 4];
        loop {
            if recv_cnt == l {
                break;
            }
            let result = MQUEUE.recv(&mut buffer, 4, 512);
            recv_cnt += 1;
            assert!(result.is_ok());
            assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
            scheduler::relinquish_me();
        }
        while TEST_SEND_CNT.load(Ordering::Acquire) != l {}
    }

    static TEST_SWITCH_CONTEXT: AtomicUsize = AtomicUsize::new(0);

    extern "C" fn test_switch_context() {
        let n = 4;
        for _i in 0..n {
            assert!(scheduler::current_thread().validate_sp());
            scheduler::yield_me();
            assert!(scheduler::current_thread().validate_sp());
        }
    }

    extern "C" fn test_switch_context_cleanup() {
        TEST_SWITCH_CONTEXT.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn stress_context_switch() {
        reset_and_queue_test_threads(test_switch_context, Some(test_switch_context_cleanup));
        loop {
            let n = TEST_SWITCH_CONTEXT.load(Ordering::Relaxed);
            if n == unsafe { TEST_THREADS.len() } {
                break;
            }
            assert!(scheduler::current_thread().validate_sp());
            scheduler::yield_me();
            assert!(scheduler::current_thread().validate_sp());
        }
    }

    static BUILT_THREADS: AtomicUsize = AtomicUsize::new(0);

    extern "C" fn do_it() {
        BUILT_THREADS.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn stress_build_threads() {
        #[cfg(target_pointer_width = "32")]
        let n = 32;
        #[cfg(all(debug_assertions, target_pointer_width = "64"))]
        let n = 32;
        #[cfg(all(not(debug_assertions), target_pointer_width = "64"))]
        let n = 512;
        for _i in 0..n {
            let t = thread::Builder::new(thread::Entry::C(do_it)).build();
            let ok = scheduler::queue_ready_thread(t.state(), t);
            assert!(ok);
        }
        loop {
            let m = BUILT_THREADS.load(Ordering::Relaxed);
            if m == n {
                break;
            }
            scheduler::yield_me();
        }
    }

    static SPAWNED_THREADS: AtomicUsize = AtomicUsize::new(0);
    #[test]
    fn stress_spawn_threads() {
        #[cfg(target_pointer_width = "32")]
        let n = 32;
        #[cfg(all(debug_assertions, target_pointer_width = "64"))]
        let n = 32;
        #[cfg(all(not(debug_assertions), target_pointer_width = "64"))]
        let n = 512;
        for _i in 0..n {
            thread::spawn(move || {
                SPAWNED_THREADS.fetch_add(1, Ordering::Relaxed);
            });
        }
        loop {
            let m = SPAWNED_THREADS.load(Ordering::Relaxed);
            if m == n {
                break;
            }
            scheduler::yield_me();
        }
    }

    // Should not hang.
    #[test]
    fn test_simple_signal() {
        let a = Arc::new(ConstBarrier::<{ 2 }>::new());
        let a_cloned = a.clone();
        let b = Arc::new(AtomicUsize::new(0));
        let b_cloned = b.clone();
        let t = crate::thread::spawn(move || {
            a.wait();
            sync::atomic_wait::atomic_wait(&b, 0, None);
        })
        .unwrap();
        // Send SIGTERM after t enters its entry function.
        a_cloned.wait();
        t.lock().kill(libc::SIGTERM as i32);
        // At this point, t is either
        // 0: waking up from a or
        // 1: is suspended on b.
        // We solve both cases by invoking yield_me and atomic_wake, which
        // should not hang.
        b_cloned.store(1, Ordering::Release);
        sync::atomic_wait::atomic_wake(&b_cloned, 1);
        scheduler::yield_me();
    }

    async fn foo(i: usize) -> usize {
        i
    }

    async fn bar() -> usize {
        42
    }

    async fn is_asynk_working() {
        let a = foo(42).await;
        let b = bar().await;
        assert_eq!(a - b, 0);
    }

    // FIXME: We still have chance falling into deadlock, TBI.
    #[test]
    fn stress_async_basic() {
        let n = 1024;
        for _i in 0..n {
            asynk::block_on(is_asynk_working());
        }
    }

    #[cfg(target_abi = "eabihf")]
    #[test]
    fn test_basic_float_add_sub() {
        let a: f32 = 1.0;
        let b = 2.0;
        let c = 3.0;
        let epsilon = 1e-6;
        assert!((a + b - c).abs() <= epsilon);
    }

    #[cfg(target_abi = "eabihf")]
    #[test]
    fn test_basic_float_mul_div() {
        let a: f32 = 2.0;
        let b = 3.0;
        let c = 6.0;
        let epsilon = 1e-6;
        assert!((a * b / c - 1.0).abs() <= epsilon);
    }

    #[inline(never)]
    pub fn kernel_unittest_runner(tests: &[&dyn Fn()]) {
        let t = scheduler::current_thread();
        #[cfg(use_defmt)]
        use defmt::println;
        #[cfg(not(use_defmt))]
        use semihosting::println;

        println!("---- Running {} kernel unittests...", tests.len());
        #[cfg(use_defmt)]
        println!(
            "Before test, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t),
            defmt::Debug2Format(&allocator::memory_info()),
            arch::current_sp(),
        );
        #[cfg(not(use_defmt))]
        println!(
            "Before test, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t),
            allocator::memory_info(),
            arch::current_sp(),
        );
        for test in tests {
            test();
        }
        #[cfg(use_defmt)]
        println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            defmt::Debug2Format(&allocator::memory_info()),
            arch::current_sp()
        );
        #[cfg(not(use_defmt))]
        println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp:  0x{:x}",
            Thread::id(&t),
            allocator::memory_info(),
            arch::current_sp()
        );
        println!("---- Done kernel unittests.");
        #[cfg(coverage)]
        crate::coverage::write_coverage_data();
        #[cfg(use_defmt)]
        cortex_m_semihosting::debug::exit(cortex_m_semihosting::debug::EXIT_SUCCESS);
    }

    #[cfg(event_flags)]
    static EVENT_COUNTER: AtomicUsize = AtomicUsize::new(0);
    #[cfg(event_flags)]
    static EVENT: sync::event_flags::EventFlags = sync::event_flags::EventFlags::new();
    #[cfg(event_flags)]
    extern "C" fn test_event_flags() {
        EVENT.wait::<scheduler::InsertToEnd>(1 << 0, sync::event_flags::EventFlagsMode::ANY, 100);
    }
    #[cfg(event_flags)]
    extern "C" fn test_event_flags_cleanup() {
        EVENT_COUNTER.fetch_add(1, Ordering::Relaxed);
    }
    #[cfg(event_flags)]
    #[test]
    fn stress_event_flags() {
        EVENT.init(0);
        reset_and_queue_test_threads(test_event_flags, Some(test_event_flags_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        loop {
            EVENT.set(1 << 0);
            let n = EVENT_COUNTER.load(Ordering::Relaxed);
            if n == l {
                break;
            }
            scheduler::yield_me();
        }
    }

    static ALLOCATOR_STRESS_THREAD1_DONE: AtomicUsize = AtomicUsize::new(0);
    static ALLOCATOR_STRESS_THREAD2_DONE: AtomicUsize = AtomicUsize::new(0);
    const MAX_TEST_HEAP_SIZE: usize = 8 * 1024 * 1024;
    fn alloc_test() {
        // Get memory info and calculate test size
        let mem_info = allocator::memory_info();
        let available = mem_info.total.saturating_sub(mem_info.used);
        let test_size = core::cmp::min(available * 3 / 4, MAX_TEST_HEAP_SIZE);

        // Test with different allocation sizes
        let sizes = [32, 64, 128, 256, 512, 1024, 2048, 4096];
        let mut allocations: Vec<Vec<u8>> = Vec::new();
        let mut current_used = 0;

        // Allocate memory in chunks
        for _ in 0..1000 {
            for &size in &sizes {
                // Check if we're using too much memory
                if current_used > test_size / 2 {
                    // Release some allocations to make room
                    while !allocations.is_empty() && current_used > test_size / 4 {
                        allocations.pop();
                        scheduler::yield_me();
                    }
                }

                // Allocate memory using Vec
                let vec = alloc::vec::Vec::<u8>::with_capacity(size);
                allocations.push(vec);
                current_used += size;

                // Yield to allow other thread to run
                scheduler::yield_me();
            }
        }

        // Clean up remaining allocations
        drop(allocations);
    }

    extern "C" fn allocator_stress_thread1() {
        alloc_test();
        ALLOCATOR_STRESS_THREAD1_DONE.store(1, Ordering::Release);
    }

    extern "C" fn allocator_stress_thread2() {
        alloc_test();
        ALLOCATOR_STRESS_THREAD2_DONE.store(1, Ordering::Release);
    }

    #[test]
    fn stress_allocator() {
        // Get initial memory info
        let initial_info = allocator::memory_info();
        let available = initial_info.total.saturating_sub(initial_info.used);
        let test_size = (available * 3) / 4;
        assert!(test_size > 0, "Not enough available memory for stress test");

        // Reset completion flags
        ALLOCATOR_STRESS_THREAD1_DONE.store(0, Ordering::Release);
        ALLOCATOR_STRESS_THREAD2_DONE.store(0, Ordering::Release);

        // Start two threads for concurrent allocation/deallocation
        let t1 = thread::Builder::new(thread::Entry::C(allocator_stress_thread1))
            .set_priority(config::MAX_THREAD_PRIORITY / 2)
            .build();
        let ok1 = scheduler::queue_ready_thread(t1.state(), t1);
        assert!(ok1);

        let t2 = thread::Builder::new(thread::Entry::C(allocator_stress_thread2))
            .set_priority(config::MAX_THREAD_PRIORITY / 2)
            .build();
        let ok2 = scheduler::queue_ready_thread(t2.state(), t2);
        assert!(ok2);

        // Wait for both threads to complete
        loop {
            let done1 = ALLOCATOR_STRESS_THREAD1_DONE.load(Ordering::Acquire);
            let done2 = ALLOCATOR_STRESS_THREAD2_DONE.load(Ordering::Acquire);
            if done1 == 1 && done2 == 1 {
                break;
            }
            scheduler::yield_me();
        }

        // Verify memory state after stress test
        let final_info = allocator::memory_info();
        // Memory should be back to a reasonable state (allowing for some fragmentation)
        assert!(
            final_info.used <= initial_info.used + test_size / 10,
            "Memory usage after stress test is too high: initial_used={}, final_used={}, test_size={}",
            initial_info.used,
            final_info.used,
            test_size
        );
    }
}
