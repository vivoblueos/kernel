// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic scope bad test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: application prepare: link application failed: LoadError \{ stage: LinkRelocate.* == 1
// COUNT: APP_LAUNCHED .*scope_bad.* == 0

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_scope_bad_test_runner)]
#![reexport_test_harness_main = "dynamic_scope_bad_test_main"]

//! Run the negative scope corpus independently. Its private DSO calls an
//! undefined weak function, which relocation policy must reject instead of
//! allowing a branch to address zero.

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::application::runtime;
use blueos_test_macro::test;
use librs::pthread;
use semihosting::println;

#[test]
fn undefined_weak_call_is_rejected() {
    let service = runtime::init();
    let mut argv = Vec::new();
    argv.push(b"/apps/scope_bad/app.elf".to_vec());
    assert!(
        service
            .spawn("/apps/scope_bad/app.elf", argv, Vec::new())
            .is_err(),
        "weak-call application must be rejected"
    );
}

#[no_mangle]
pub fn dynamic_scope_bad_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic scope bad test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic scope bad test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_scope_bad_test_main();
    0
}
