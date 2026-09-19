// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic Clang CXX test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/clang_cxx/lib/libclang_cxx_private\.so\.1 == 1
// COUNT: APP_LAUNCHED handle=.* path=/apps/clang_cxx/app\.elf == 1
// COUNT: APP_REAP handle=.* private_images=2 imported_dsos=1 == 1
// COUNT: clang-cxx: private ctor state=37 == 1
// COUNT: clang-cxx: result=49 argc=2 argv1=blueos == 1
// COUNT: clang-cxx: private fini state=37 == 1

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_clang_cxx_test_runner)]
#![reexport_test_harness_main = "dynamic_clang_cxx_test_main"]

//! Run a Clang-built C++ PIE whose private C++ DSO and root both import the
//! shared `libc.so.1`. This proves the language-neutral ARM32 loader contract,
//! private-name search, lifecycle arrays, argv delivery and full group reap.

extern crate alloc;
extern crate rsrt;

use alloc::{vec, vec::Vec};
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

fn launch_and_wait(service: &ApplicationService) {
    let argv = vec![b"/apps/clang_cxx/app.elf".to_vec(), b"blueos".to_vec()];
    let handle = service
        .spawn("/apps/clang_cxx/app.elf", argv, Vec::new())
        .expect("spawn Clang C++ app");

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
    panic!("Clang C++ app was not reaped within the wait bound");
}

#[test]
fn clang_cxx_private_dso_vertical() {
    launch_and_wait(runtime::init());
}

#[no_mangle]
pub fn dynamic_clang_cxx_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic Clang CXX test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic Clang CXX test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_clang_cxx_test_main();
    0
}
