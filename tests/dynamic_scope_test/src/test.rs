// NEWLINE-TIMEOUT: 10
// ASSERT-SUCC: Dynamic scope test ended
// ASSERT-FAIL: Backtrace in Panic.*
// ASSERT-FAIL: ASSERTION FAILED.*
// COUNT: DSO_LOAD path=/system/lib/libscope_sys\.so\.1 == 3
// COUNT: DSO_LOAD path=/system/lib/libc\.so\.1 == 1
// COUNT: DSO_REUSE path=/system/lib/libscope_sys\.so\.1 == 1
// COUNT: DSO_UNLOAD path=/system/lib/libscope_sys\.so\.1 == 3
// COUNT: DSO_FINI path=/system/lib/libscope_sys\.so\.1 == 3
// COUNT: DSO_REUSE path=/system/lib/libc\.so\.1 == 3
// COUNT: LINK_MAP owner=7 soname=- .* == 4
// COUNT: NS_LOAD path=/apps/scope_demo/lib/libweak\.so\.1 == 4
// COUNT: NS_LOAD path=/apps/scope_demo/lib/libstrong\.so\.1 == 4
// COUNT: NS_LOAD path=/apps/scope_demo/lib/libhidden\.so\.1 == 4
// COUNT: NS_LOAD path=/apps/scope_demo/lib/libprotected\.so\.1 == 4
// COUNT: NS_LOAD path=/apps/scope_demo/lib/libweakdata\.so\.1 == 4
// COUNT: APP_LAUNCHED handle=.* path=/apps/scope_demo/app\.elf == 4
// COUNT: APP_REAP handle=.* private_images=6 imported_dsos=2 == 4
// COUNT: scope: value=111 fn=1110 hidden=555 hidden_report=999 protected=333 self=444 sys=777 sys_target=42 sys_ctor=1 weakdata=0 == 4
// COUNT: SCOPE_BIND requester=.* name=missing_data provider=none == 4
// COUNT: SCOPE_BIND requester=7 name=sys_target provider=7 == 3
// COUNT: SCOPE_BIND requester=7 name=strlen provider=1 == 3
// COUNT: LINK_EDGE requester=7 provider=1 == 3

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(dynamic_scope_test_runner)]
#![reexport_test_harness_main = "dynamic_scope_test_main"]

//! scope/visibility end-to-end test: the frozen application scope
//! decisions, observed through real Thumb ELF artifacts.
//!
//! The scope corpus bundle (`apps/example/dynamic/scope_demo`) exercises:
//!
//! * strong over weak — libweak (SysV `DT_HASH`) is discovered first, but its
//! weak `scope_value`/`scope_fn` lose to libstrong's strong definitions;
//! * hidden — libhidden's hidden `hidden_probe` never leaks into the scope
//! (libstrong's strong one binds; the owner's `hidden_report` reads its own);
//! * protected — libprotected's owner-local `self_value` binding wins over the
//! root's interposing strong definition;
//! * app interpose — the root's own definitions bind root-first;
//! * system non-interpose — the freshly loaded system DSO's `sys_target`
//! relocation binds its own definition (SCOPE_BIND requester=7 provider=7)
//! even though the root defines a same-named symbol;
//! * undefined weak data — `missing_data` binds to zero
//! (SCOPE_BIND provider=none; the app prints weakdata=0).
//! * atomic concurrent acquisition — two linker workers race the same system
//! closure and share one `libscope_sys` instance;

extern crate alloc;
extern crate rsrt;

use alloc::vec::Vec;
use blueos::{
    application::{runtime, service::ApplicationService},
    scheduler,
    thread::{Builder, Entry, Stack, IDLE},
};
use blueos_test_macro::test;
use core::sync::atomic::{AtomicUsize, Ordering};
use librs::pthread;
use semihosting::println;

/// Launch an application and wait (bounded) for the deferred reaper to recycle its
/// slot. Returns the handle whose generation the relaunch assertion compares.
fn launch_and_wait(
    service: &ApplicationService,
    path: &str,
) -> blueos::application::manager::ApplicationHandle {
    let mut argv = Vec::new();
    argv.push(path.as_bytes().to_vec());
    let handle = service
        .spawn(path, argv, Vec::new())
        .expect("spawn scope app");

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
fn scope_visibility_vertical() {
    // Boot installed the embedded corpus artifacts and initialized the runtime
    //; this idempotent call retrieves the same service without
    // reseeding the VFS.
    let service = runtime::init();

    // The scope corpus application: all bindings are asserted by the checker
    // through the app's printed values and the SCOPE_BIND diagnostic lines.
    // First launch: loads libscope_sys fresh (constructor runs); after the
    // group exits, the reaper runs the system fini on its worker thread and
    // unloads the instance.
    let first = launch_and_wait(service, "/apps/scope_demo/app.elf");
    assert_eq!(first.slot, 0, "the first test app takes slot 0");

    // Second launch: the unloaded slot reloads generation+1 (constructor runs
    // again); the checker asserts the init/fini/unload diagnostic lines.
    let second = launch_and_wait(service, "/apps/scope_demo/app.elf");
    assert_eq!(first.slot, second.slot, "slot must be recycled");
    assert_ne!(
        first.generation, second.generation,
        "generation must bump on relaunch"
    );

    // Two kernel threads now race the same system closure. Besides proving
    // that batch acquisition has no partial-wait deadlock, this exercises a
    // shared Ready instance and the last-user unload path concurrently.
    concurrent_system_closure();
}

/// Two kernel threads spawn the scope app simultaneously: each
/// launches and waits for its group's reap, then signals completion.
/// The two racer threads' bodies: launch the scope app, wait for the
/// reap, then set the completion flag the main thread polls.
extern "C" fn concurrent_launcher(flag: *mut core::ffi::c_void) {
    let done = flag as *const core::sync::atomic::AtomicBool;
    let service = ApplicationService::get().expect("service assembled");
    let mut argv = Vec::new();
    argv.push(b"/apps/scope_demo/app.elf".to_vec());
    let handle = service
        .spawn("/apps/scope_demo/app.elf", argv, Vec::new())
        .expect("concurrent spawn");
    static WAIT_ATOM: AtomicUsize = AtomicUsize::new(0);
    for _ in 0..600 {
        if !service.manager().contains(handle) {
            unsafe { (*done).store(true, Ordering::Release) };
            return;
        }
        let _ = blueos::sync::atomic_wait(
            &WAIT_ATOM,
            WAIT_ATOM.load(Ordering::Acquire),
            blueos::time::Tick::from_millis(50),
        );
    }
    panic!("concurrent app was not reaped");
}

fn concurrent_system_closure() {
    const LINKER_WORKER_STACK_SIZE: usize = 64 << 10;
    static DONE_A: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);
    static DONE_B: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(false);
    static WAIT_ATOM: AtomicUsize = AtomicUsize::new(0);

    let a = Builder::new(Entry::Posix(
        concurrent_launcher,
        &DONE_A as *const _ as *mut core::ffi::c_void,
    ))
    .set_stack(Stack::from_size(LINKER_WORKER_STACK_SIZE).expect("linker worker stack"))
    .build();
    let b = Builder::new(Entry::Posix(
        concurrent_launcher,
        &DONE_B as *const _ as *mut core::ffi::c_void,
    ))
    .set_stack(Stack::from_size(LINKER_WORKER_STACK_SIZE).expect("linker worker stack"))
    .build();
    let _ = scheduler::queue_ready_thread(IDLE, a);
    let _ = scheduler::queue_ready_thread(IDLE, b);
    while !DONE_A.load(Ordering::Acquire) || !DONE_B.load(Ordering::Acquire) {
        let _ = blueos::sync::atomic_wait(
            &WAIT_ATOM,
            WAIT_ATOM.load(Ordering::Acquire),
            blueos::time::Tick::from_millis(10),
        );
    }
}

#[no_mangle]
pub fn dynamic_scope_test_runner(tests: &[&dyn Fn()]) {
    println!("Dynamic scope test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Dynamic scope test ended");
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::application::seed::install();
    pthread::register_my_posix_tcb();
    dynamic_scope_test_main();
    0
}
