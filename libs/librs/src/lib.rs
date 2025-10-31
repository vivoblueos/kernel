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

#![cfg_attr(not(std), no_std)]
#![cfg_attr(test, feature(custom_test_frameworks))]
#![cfg_attr(test, test_runner(librs_test_runner))]
#![cfg_attr(test, reexport_test_harness_main = "librs_test_main")]
#![cfg_attr(test, no_main)]
#![allow(internal_features)]
#![feature(c_size_t)]
#![feature(slice_internals)]
#![feature(ptr_as_uninit)]
#![feature(linkage)]
#![feature(lang_items)]
#![feature(thread_local)]
#![feature(box_as_ptr)]
#![feature(atomic_from_mut)]
#![feature(c_variadic)]
#![feature(array_ptr_get)]

#[macro_use]
extern crate alloc;
#[cfg(test)]
extern crate rsrt;
// We don't expose any interfaces or types externally, rust-lang/libc is doing that.
pub mod c_str;
pub mod ctype;
pub mod direct;
pub mod errno;
pub mod fcntl;
pub mod io;
pub mod iter;
pub mod misc;
pub mod mqueue;
pub mod net;
pub mod pthread;
pub mod sched;
pub mod semaphore;
pub mod signal;
pub mod stat;
pub mod stdio;
pub mod stdlib;
pub mod string;
pub mod sync;
pub mod sys_mmap;
pub mod syscall;
pub mod time;
pub mod tls;
pub mod types;
pub mod unistd;
extern "C" fn start_blueos_posix_main(_arg: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    // TODO: Pass argc, argv and envp?
    // TODO: Before exit, we have to check owned threads' status and recycle them.
    extern "C" {
        fn main() -> i32;
    }
    unsafe {
        main();
    }
    core::ptr::null_mut()
}

// TODO: Implement crt*.o.
#[no_mangle]
pub extern "C" fn start_blueos_posix() {
    let mut init_thread: libc::pthread_t = 0;
    let rc = crate::pthread::pthread_create(
        &mut init_thread as *mut libc::pthread_t,
        core::ptr::null(),
        start_blueos_posix_main,
        core::ptr::null_mut(),
    );
    assert_eq!(rc, 0);
    // TODO: check rc to take failure action.
    crate::pthread::pthread_join(init_thread, core::ptr::null_mut());
}

extern "C" fn start_posix_main(_arg: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    // TODO: Pass argc, argv and envp?
    // TODO: Before exit, we have to check owned threads' status and recycle them.
    extern "C" {
        fn main() -> i32;
    }
    unsafe {
        main();
    }
    core::ptr::null_mut()
}

#[no_mangle]
pub extern "C" fn __librs_start_main() {
    crate::stdio::init();
    let mut init_thread: libc::pthread_t = 0;
    let rc = crate::pthread::pthread_create(
        &mut init_thread as *mut libc::pthread_t,
        core::ptr::null(),
        start_posix_main,
        core::ptr::null_mut(),
    );
    assert_eq!(rc, 0);
    crate::pthread::pthread_join(init_thread, core::ptr::null_mut());
}

// FIXME: Remove this when we have a proper libc implementation.
#[cfg(feature = "linux_emulation")]
#[path = "../tests/linux_emulation_test/utils.rs"]
pub mod utils;

#[cfg(target_arch = "arm")]
#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn __aeabi_unwind_cpp_pr0() {
    panic!("Unwind not implemented")
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn _Unwind_Backtrace(
    _trace: *mut core::ffi::c_void,
    _arg: *mut core::ffi::c_void,
) -> core::ffi::c_int {
    todo!()
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn _Unwind_GetIP(_context: *mut core::ffi::c_void) -> core::ffi::c_int {
    todo!()
}

#[cfg(test)]
use semihosting::println;

#[cfg(test)]
pub fn librs_test_runner(tests: &[&dyn Fn()]) {
    println!("Librs unittest started");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Librs unittest ended");

    #[cfg(coverage)]
    blueos::coverage::write_coverage_data();
}

#[cfg(test)]
extern "C" fn posix_main(_: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    librs_test_main();
    core::ptr::null_mut()
}

#[cfg(test)]
#[no_mangle]
extern "C" fn main() -> i32 {
    use libc::pthread_t;
    use pthread::{pthread_create, pthread_join};
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
    0
}
