// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic cycle test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/cycle_demo/lib/libcycle_a\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/cycle_demo/lib/libcycle_b\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/cycle_demo/lib/libcommon\.so\.1 == 1
// COUNT: APP_LAUNCHED handle=.* path=/apps/cycle_demo/app\.elf == 1
// COUNT: APP_REAP handle=.* private_images=4 imported_dsos=1 == 1
// COUNT: cycle: value=82 a_ctor=1 b_ctor=1 == 1
// COUNT: LIFECYCLE_SCC group=.* members=\[2, 3\] == 1
// COUNT: LIFECYCLE_INIT index=0 owner=2 == 1
// COUNT: LIFECYCLE_INIT index=1 owner=3 == 1
// COUNT: LIFECYCLE_GROUP_FINI index=0 owner=3 == 1
// COUNT: LIFECYCLE_GROUP_FINI index=1 owner=2 == 1

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_cycle_test_runner)]
#![reexport_test_harness_main = "dynamic_cycle_test_main"]

//! Run the private A <-> B ELF dependency cycle through the application
//! service. The checker verifies SCC discovery and dependency-first lifecycle
//! ordering against the real runtime artifacts.

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

fn launch_and_wait(service: &ApplicationService) {
    let mut argv = Vec::new();
    argv.push(b"/apps/cycle_demo/app.elf".to_vec());
    let handle = service
        .spawn("/apps/cycle_demo/app.elf", argv, Vec::new())
        .expect("spawn cycle app");

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
    panic!("cycle app was not reaped within the wait bound");
}

#[test]
fn private_cycle_vertical() {
    launch_and_wait(runtime::init());
}

#[no_mangle]
pub fn dynamic_cycle_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic cycle test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic cycle test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_cycle_test_main();
    0
}
