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

pub mod ffi {
    #[coverage(off)]
    #[no_mangle]
    pub extern "C" fn disable_local_irq_save() -> usize {
        crate::arch::disable_local_irq_save()
    }

    #[coverage(off)]
    #[no_mangle]
    pub extern "C" fn enable_local_irq_restore(val: usize) {
        crate::arch::enable_local_irq_restore(val)
    }

    #[coverage(off)]
    #[no_mangle]
    #[linkage = "weak"]
    pub unsafe extern "C" fn __aeabi_memclr8(s: *mut u8, n: usize) -> *mut u8 {
        let mut i = 0;
        for i in 0..n {
            s.add(i).write(0u8);
        }
        s
    }
}

pub mod allocator;
pub(crate) mod arch;
pub mod asynk;
pub(crate) mod boards;
pub(crate) mod boot;
pub(crate) mod config;
pub(crate) mod console;
#[cfg(coverage)]
pub mod coverage;
pub(crate) mod devices;
pub(crate) mod drivers;
pub mod error;
pub(crate) mod irq;
pub(crate) mod logger;
pub mod net;
pub mod scheduler;
pub mod support;
pub mod sync;
pub mod syscall_handlers;
pub mod thread;
pub(crate) mod time;
pub mod types;
pub mod vfs;

pub use syscall_handlers as syscalls;

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
        time::WAITING_FOREVER, types::Arc,
    };
    use blueos_header::syscalls::NR::Nop;
    use blueos_kconfig::NUM_CORES;
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
        let tick = time::get_sys_ticks();
        assert!(scheduler::current_thread().validate_sp());
        scheduler::suspend_me_for(10);
        assert!(scheduler::current_thread().validate_sp());
        let tick2 = time::get_sys_ticks();
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

    static mut SEMA_COUNTER: usize = 0usize;
    static SEMA: sync::semaphore::Semaphore = sync::semaphore::Semaphore::new(1);

    extern "C" fn test_semaphore() {
        SEMA.acquire_notimeout();
        let n = unsafe { SEMA_COUNTER };
        unsafe { SEMA_COUNTER += 1 };
    }

    extern "C" fn test_semaphore_cleanup() {
        SEMA.release();
    }

    #[test]
    fn stress_semaphore() {
        SEMA.init();
        reset_and_queue_test_threads(test_semaphore, Some(test_semaphore_cleanup));
        let l = unsafe { TEST_THREADS.len() };
        loop {
            SEMA.acquire_notimeout();
            let n = unsafe { SEMA_COUNTER };
            if n == l {
                SEMA.release();
                break;
            }
            SEMA.release();
            scheduler::yield_me();
        }
    }

    static TEST_ATOMIC_WAIT: AtomicUsize = AtomicUsize::new(0);

    extern "C" fn test_atomic_wait_cleanup() {
        TEST_ATOMIC_WAIT.fetch_add(1, Ordering::Release);
        sync::atomic_wait::atomic_wake(&TEST_ATOMIC_WAIT, 1);
    }

    extern "C" fn test_atomic_wait() {}

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
            scheduler::yield_me();
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
            defmt::Debug2Format(&ALLOCATOR.memory_info()),
            arch::current_sp(),
        );
        #[cfg(not(use_defmt))]
        println!(
            "Before test, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t),
            ALLOCATOR.memory_info(),
            arch::current_sp(),
        );
        for test in tests {
            test();
        }
        #[cfg(use_defmt)]
        println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            defmt::Debug2Format(&ALLOCATOR.memory_info()),
            arch::current_sp()
        );
        #[cfg(not(use_defmt))]
        println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp:  0x{:x}",
            Thread::id(&t),
            ALLOCATOR.memory_info(),
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
        EVENT.wait(1 << 0, sync::event_flags::EventFlagsMode::ANY, 100);
        EVENT_COUNTER.fetch_add(1, Ordering::Relaxed);
    }
    #[cfg(event_flags)]
    #[test]
    fn stress_event_flags() {
        EVENT.init(0);
        reset_and_queue_test_threads(test_event_flags, None);
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
}
