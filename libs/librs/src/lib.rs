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
#![feature(sync_unsafe_cell)]

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

#[no_mangle]
pub extern "C" fn __librs_start_main() {
    crate::pthread::register_my_tcb();
    crate::stdio::init();
    // TODO: Pass argc, argv and envp?
    // TODO: Before exit, we have to check owned threads' status and recycle them.
    extern "C" {
        fn main() -> i32;
    }
    unsafe {
        main();
    }
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
#[no_mangle]
extern "C" fn main() -> i32 {
    pthread::register_my_tcb();
    librs_test_main();
    0
}
