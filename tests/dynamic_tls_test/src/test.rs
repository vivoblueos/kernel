// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic TLS test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/tls_demo/lib/libfoo\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/tls_demo/lib/libbar\.so\.1 == 1
// COUNT: APP_LAUNCHED handle=.* path=/apps/tls_demo/app\.elf == 1
// COUNT: APP_REAP handle=.* private_images=3 imported_dsos=1 == 1
// COUNT: tls: a_foo=7 a_bar=7 b_foo=13 b_bar=13 repeat=1 == 1

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_tls_test_runner)]
#![reexport_test_harness_main = "dynamic_tls_test_main"]

//! Run the emutls corpus independently. The application repeatedly creates
//! and joins pthreads and proves per-image control identity plus per-thread
//! value isolation.

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
    argv.push(b"/apps/tls_demo/app.elf".to_vec());
    let handle = service
        .spawn("/apps/tls_demo/app.elf", argv, Vec::new())
        .expect("spawn TLS app");

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
fn emutls_vertical() {
    launch_and_wait(runtime::init());
}

#[no_mangle]
pub fn dynamic_tls_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic TLS test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic TLS test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_tls_test_main();
    0
}
