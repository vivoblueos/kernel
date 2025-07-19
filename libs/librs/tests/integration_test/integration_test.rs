// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![no_main]
#![no_std]
#![feature(custom_test_frameworks)]
#![test_runner(librs_test_runner)]
#![reexport_test_harness_main = "librs_test_main"]
#![feature(c_size_t)]
#![feature(thread_local)]
#![feature(c_variadic)]

extern crate rsrt;

use blueos::{allocator, thread::Thread};
use core::ffi::c_void;
use libc::pthread_t;
use librs::pthread::{pthread_create, pthread_join, pthread_self};
use semihosting::println;

mod ctype;
mod pthread;
mod scal;

#[inline(never)]
fn librs_test_runner(tests: &[&dyn Fn()]) {
    println!("Librs integration test started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Librs integration test ended");
}

extern "C" fn posix_main(_: *mut c_void) -> *mut c_void {
    librs_test_main();
    core::ptr::null_mut()
}

#[no_mangle]
fn main() -> i32 {
    // We must enter POSIX subsystem first to perform pthread testing.
    let mut t: pthread_t = 0;
    let rc = pthread_create(
        &mut t as *mut pthread_t,
        core::ptr::null(),
        posix_main,
        core::ptr::null_mut(),
    );
    assert_eq!(rc, 0);
    pthread_join(t, core::ptr::null_mut());

    #[cfg(coverage)]
    blueos::coverage::write_coverage_data();
    0
}
