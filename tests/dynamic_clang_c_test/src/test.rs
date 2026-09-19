// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic Clang C test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: NS_LOAD path=/apps/clang_c/lib/libclang_c_private\.so\.1 == 1
// COUNT: APP_LAUNCHED handle=.* path=/apps/clang_c/app\.elf == 1
// COUNT: APP_REAP handle=.* private_images=2 imported_dsos=1 == 1
// COUNT: clang-c: private ctor state=37 == 1
// COUNT: clang-c: base=37 generation=1 == 1
// COUNT: clang-c: result=49 argc=2 argv1=blueos argv1len=6 == 1
// COUNT: clang-c: heap ok=1 == 1
// COUNT: clang-c: private fini state=37 == 1

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_clang_c_test_runner)]
#![reexport_test_harness_main = "dynamic_clang_c_test_main"]

//! Run a Clang-built **C** PIE whose private C DSO and root both import the
//! shared `libc.so.1`.
//!
//! Everything else in the dynamic corpus is Rust or freestanding C++, which
//! left "does the loader run a plain C program?" as an inference from the
//! language-neutral ELF contract rather than a result. This test makes it a
//! result. The C app exercises what the C++ fixture does not: `malloc`/`free`
//! across the DSO boundary, `strlen`/`memcpy`/`memcmp` reached through the PLT,
//! a root-owned BSS word initialized by the root's own constructor, and reads
//! of a data object owned by the private DSO.

extern crate alloc;
extern crate rsrt;

use alloc::{vec, vec::Vec};
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

fn launch_and_wait(service: &ApplicationService) {
    let argv = vec![b"/apps/clang_c/app.elf".to_vec(), b"blueos".to_vec()];
    let handle = service
        .spawn("/apps/clang_c/app.elf", argv, Vec::new())
        .expect("spawn Clang C app");

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
    panic!("Clang C app was not reaped within the wait bound");
}

#[test]
fn clang_c_private_dso_vertical() {
    launch_and_wait(runtime::init());
}

#[no_mangle]
pub fn dynamic_clang_c_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic C test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic Clang C test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_clang_c_test_main();
    0
}
