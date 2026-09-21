// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic stack reclaim test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// CHECK-SUCC: STACK_RECLAIM round=1
// CHECK-SUCC: STACK_RECLAIM round=2
// CHECK-SUCC: STACK_RECLAIM round=3

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(stack_reclaim_test_runner)]
#![reexport_test_harness_main = "stack_reclaim_test_main"]

//! Prove that all per-launch resources, including pthread stacks, come back.
//!
//! A dynamic application allocates its own thread stacks and the kernel only
//! borrows them: the cleanup that returns the storage to the libc allocator
//! runs on the application reaper, an ordinary thread, because the scheduler
//! reaches retirement from the context-switch path where the `svc` that
//! allocator needs is not available.
//!
//! A cleanup that never runs leaks a whole stack per thread and reports
//! nothing. A strong reference left in either non-returning exit frame leaks a
//! much smaller fixed set of blocks. This test launches the pthread-heavy
//! fixture repeatedly and requires the steady-state heap not to drift upwards
//! between rounds.

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

/// The fixture that creates and joins pthreads, already seeded into the root
/// tmpfs by the boot seed catalog.
const FIXTURE: &str = "/apps/tls_demo/app.elf";

/// Rounds compared against each other, after one warm-up launch.
const ROUNDS: usize = 3;

/// Steady-state launches must be allocation-neutral after the reaper removed
/// the manager slot. The warm-up below absorbs cached system DSOs and one-time
/// allocator/runtime setup, so even a single retained slab block is a failure.
const DRIFT_TOLERANCE: usize = 0;

fn heap_used() -> usize {
    blueos::allocator::memory_info().used
}

fn launch_fixture(service: &ApplicationService) {
    let mut argv = Vec::new();
    argv.push(FIXTURE.as_bytes().to_vec());
    let handle = service
        .spawn(FIXTURE, argv, Vec::new())
        .expect("spawn TLS app");

    // Bounded poll: the reaper scans every REAPER_POLL_MILLIS and the fixture
    // exits within milliseconds of starting.
    static WAIT_ATOM: AtomicUsize = AtomicUsize::new(0);
    for _ in 0..600 {
        if !service.manager().contains(handle) {
            return;
        }
        let _ = blueos::sync::atomic_wait(
            &WAIT_ATOM,
            WAIT_ATOM.load(Ordering::Acquire),
            blueos::time::Tick::from_millis(50),
        );
    }
    panic!("TLS app was not reaped within the wait bound");
}

#[test]
fn application_launch_resources_are_reclaimed() {
    let service = runtime::init();

    // Warm-up: the first launch is the loading generation for `libc.so.1` and
    // the fixture's private DSOs, which stay resident for the later launches.
    // Measuring it would compare an image-loading footprint against a
    // steady-state one.
    launch_fixture(service);
    let mut previous = heap_used();

    for round in 1..=ROUNDS {
        launch_fixture(service);
        let used = heap_used();
        println!("STACK_RECLAIM round={round} used={used}");
        assert!(
            used <= previous + DRIFT_TOLERANCE,
            "round {round}: heap grew by {} bytes since the previous round; \
             per-launch resources were not fully reclaimed",
            used.saturating_sub(previous)
        );
        previous = used;
    }
}

#[no_mangle]
pub fn stack_reclaim_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic stack reclaim test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic stack reclaim test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    stack_reclaim_test_main();
    0
}
