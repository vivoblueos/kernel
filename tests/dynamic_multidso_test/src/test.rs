// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic multidso test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: DSO_REUSE path=/system/lib/libc\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/multi/lib/libfoo\.so\.1 == 2
// COUNT: NS_LOAD path=/apps/multi/lib/libbar\.so\.1 == 2
// COUNT: NS_LOAD path=/apps/multi/lib/libcommon\.so\.1 == 2
// COUNT: APP_LAUNCHED handle=.*:1 path=/apps/multi/app\.elf == 1
// COUNT: APP_LAUNCHED handle=.*:2 path=/apps/multi/app\.elf == 1
// COUNT: APP_REAP handle=.*:1 private_images=4 imported_dsos=1 == 1
// COUNT: APP_REAP handle=.*:2 private_images=4 imported_dsos=1 == 1
// COUNT: multi: foo=42 bar=80 == 2
// COUNT: LIFECYCLE_INIT index=0 owner=4 == 2
// COUNT: LIFECYCLE_INIT index=1 owner=3 == 2
// COUNT: LIFECYCLE_INIT index=2 owner=2 == 2
// COUNT: LIFECYCLE_GROUP_FINI index=0 owner=2 == 2
// COUNT: LIFECYCLE_GROUP_FINI index=1 owner=3 == 2
// COUNT: LIFECYCLE_GROUP_FINI index=2 owner=4 == 2
// COUNT: LIFECYCLE_SYSTEM_FINI .* == 0

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_multidso_test_runner)]
#![reexport_test_harness_main = "dynamic_multidso_test_main"]
#![feature(c_size_t)]

//! Launch a real multi-DSO application through the runtime namespace path —
//! read-only dependency planning, atomic system batch acquire, private DSO
//! search, ARM32 NOW
//! relocation, private init/fini ordering, application exit and deferred
//! reaping — on `qemu_mps2_an385`.
//!
//! The bundle (`apps/example/dynamic/multi_dso`: root + foo/bar/common
//! private DSOs, all importing the shared libc) is streamed from the host and
//! seeded into the root tmpfs by this image's `main` entry, before the boot
//! seed entry point, so the test exercises the same boot path a real boot
//! uses. The checker counts the diagnostic lines:
//!
//! * each private identity maps exactly once per group — foo and bar both
//! `DT_NEEDED` libcommon, but the diamond loads it a single time (one
//! `NS_LOAD` line per resolved path per launch);
//! * each group's exit releases all four private allocations (root + foo +
//! bar + common) in exactly one reap (`APP_REAP ... private_images=4`).
//!
//! Launching the application twice additionally proves per-group private state:
//! the second group maps the same private DSOs again instead of sharing the
//! first group's relocated images.

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

/// Launch the multi app and wait (bounded) for the deferred reaper to
/// recycle its slot, then assert the public state is gone. Returns the handle
/// whose generation the relaunch assertion compares against.
fn launch_and_wait(
    service: &ApplicationService,
) -> blueos::application::manager::ApplicationHandle {
    let mut argv = Vec::new();
    argv.push(b"/apps/multi/app.elf".to_vec());
    let handle = service
        .spawn("/apps/multi/app.elf", argv, Vec::new())
        .expect("spawn multi app");

    // Bounded poll: the reaper scans every REAPER_POLL_MILLIS and the app
    // exits within milliseconds of starting.
    static WAIT_ATOM: AtomicUsize = AtomicUsize::new(0);
    for _ in 0..600 {
        if !service.manager().contains(handle) {
            return handle;
        }
        let _ = blueos::sync::atomic_wait(
            &WAIT_ATOM,
            WAIT_ATOM.load(Ordering::Acquire),
            blueos::time::Tick::from_millis(50),
        );
    }
    panic!("multi app was not reaped within the wait bound");
}

#[test]
fn multidso_namespace_vertical() {
    // Boot installed the embedded bundle artifacts and initialized the
    // runtime; this idempotent call retrieves the same service without
    // reseeding the VFS.
    let service = runtime::init();

    // First launch: this link is the first loading generation for libc.so.1
    // (DSO_LOAD); the namespace planner walks the ELF closure (root ->
    // foo/bar -> common, system edges on libc) and the group is
    // reaped with all four private allocations and its one imported lease.
    let first = launch_and_wait(service);

    // Second launch: the Ready libc instance is imported (DSO_REUSE) and the
    // private DSOs map again into the fresh group; the slot is
    // recycled with a bumped generation.
    let second = launch_and_wait(service);
    assert_eq!(first.slot, second.slot, "slot must be recycled");
    assert_ne!(
        first.generation, second.generation,
        "generation must bump on relaunch"
    );
}

#[no_mangle]
pub fn dynamic_multidso_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic multidso test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic multidso test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_multidso_test_main();
    0
}
