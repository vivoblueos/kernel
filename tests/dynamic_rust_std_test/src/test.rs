// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic Rust std test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// ASSERT-FAIL: libc: abort\(\)
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: APP_LAUNCHED handle=.* path=/apps/rust_std/app\.elf == 1
// COUNT: APP_REAP handle=.* private_images=1 imported_dsos=1 == 1
// COUNT: rust-std: hello == 1
// COUNT: rust-std: sum=56 len=8 == 1
// COUNT: rust-std: joined=0,2,4,6,8,10,12,14 == 1
// COUNT: rust-std: thread=ThreadId\( == 1

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_rust_std_test_runner)]
#![reexport_test_harness_main = "dynamic_rust_std_test_main"]

//! Run a Rust **`std`** PIE whose only dynamic dependency is the shared
//! `libc.so.1`.
//!
//! The other Rust fixtures are `no_std`: they pin the ELF and relocation
//! contract but never start `std`'s runtime. This one does. `std` is linked
//! statically into the image, so what has to work is `std`'s `lang_start`, its
//! lazy initializers, its allocator's `calloc`/`realloc`/`memalign` path and
//! `std::io::stdout` — all against the shared libc, reached through the same
//! loader contract the C and C++ fixtures use.
//!
//! It also covers the bootstrap seam the other fixtures do not: `std` brings
//! its own `main` wrapper, while the entry is still
//! `blueos_scrt1::_start -> __librs_start_main(main, info)`.

extern crate alloc;
extern crate rsrt;

use alloc::{vec, vec::Vec};
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

fn launch_and_wait(service: &ApplicationService) {
    let argv = vec![b"/apps/rust_std/app.elf".to_vec()];
    let handle = service
        .spawn("/apps/rust_std/app.elf", argv, Vec::new())
        .expect("spawn Rust std app");

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
    panic!("Rust std app was not reaped within the wait bound");
}

#[test]
fn rust_std_vertical() {
    launch_and_wait(runtime::init());
}

#[no_mangle]
pub fn dynamic_rust_std_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic Rust std test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic Rust std test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_rust_std_test_main();
    0
}
