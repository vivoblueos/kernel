// NEWLINE-TIMEOUT: 10
// CHECK-SUCC: Dynamic application test started
// CHECK-SUCC: DSO_LOAD path=/system/lib/libc.so.1
// CHECK-SUCC: hello dynamic app
// CHECK-SUCC: argv0=/apps/hello/app.elf
// CHECK-SUCC: argv0=app.elf
// CHECK-SUCC: auxv: AT_PHDR ok
// CHECK-SUCC: APP_LAUNCHED handle=.* path=/apps/hello/app.elf
// CHECK-SUCC: APP_INIT_COMPLETE handle=.*
// CHECK-SUCC: APP_REAP handle=.* private_images=1 imported_dsos=1
// CHECK-SUCC: DSO_REUSE path=/system/lib/libc.so.1
// ASSERT-SUCC: Dynamic application test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_test_runner)]
#![reexport_test_harness_main = "dynamic_test_main"]
#![feature(c_size_t)]

//! end-to-end: launch a real Thumb PIE dynamic application through the
//! full kernel path — VFS snapshot, dependency closure, `libc.so.1` load,
//! ARM32 NOW relocation, thread entry, `scrt1`/`librs` startup, application
//! exit and deferred reaping — on `qemu_mps2_an385`.
//!
//! The system image (`apps/example/dynamic/hello` and `librs:libc`) is
//! streamed from the host by the build's boot seed catalog and seeded into the root tmpfs
//! by the boot seed entry point, so the test exercises the same boot path a
//! real boot uses.

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::application::{runtime, service::ApplicationService};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

/// Launch the hello app and wait (bounded) for the deferred reaper to recycle
/// its slot, then assert the public state is gone. Returns the handle whose
/// generation the relaunch assertion compares against.
fn launch_and_wait(
    service: &ApplicationService,
    path: &str,
    argc1: bool,
) -> blueos::application::manager::ApplicationHandle {
    let mut argv = Vec::new();
    argv.push(path.as_bytes().to_vec());
    if argc1 {
        argv.push(b"arg1".to_vec());
    }
    let handle = service
        .spawn(path, argv, Vec::new())
        .expect("spawn dynamic app");

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
    panic!("application was not reaped within the wait bound");
}

#[test]
fn dynamic_app_vertical() {
    // Boot installed the embedded artifacts and initialized the runtime
    //; this idempotent call retrieves the same service without
    // reseeding the VFS.
    let service = runtime::init();

    // First launch: this link is the first loading generation for libc.so.1
    // (DSO_LOAD), the app runs its main through the shared libc, exits and is
    // reaped with its private image and its one imported libc lease.
    let first = launch_and_wait(service, "/apps/hello/app.elf", true);

    // Second launch: the Ready libc instance is imported (DSO_REUSE), not
    // remapped. Change cwd and use a relative launch path to exercise the
    // service's one-time pwd snapshot; its log still reports the normalized
    // absolute identity. The slot is recycled with a bumped generation.
    assert_eq!(
        blueos::vfs::syscalls::chdir(b"/apps/hello\0".as_ptr().cast()),
        0
    );
    let second = launch_and_wait(service, "app.elf", false);
    assert_eq!(first.slot, second.slot, "slot must be recycled");
    assert_ne!(
        first.generation, second.generation,
        "generation must bump on relaunch"
    );
}

#[no_mangle]
pub fn dynamic_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic application test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic application test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_test_main();
    0
}
