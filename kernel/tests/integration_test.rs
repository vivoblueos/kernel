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
#![test_runner(kernel_test_runner)]
#![reexport_test_harness_main = "kernel_test_main"]

extern crate alloc;
extern crate rsrt;
use blueos::allocator;
use semihosting::println;

#[cfg(enable_net)]
mod net;
mod test_futex;
/// Unstable rust custom test framework test file hierarchy.
/// Since there is no cargo framework, we manually set it up.
mod test_semaphore;
#[cfg(enable_vfs)]
mod test_vfs;

/// Unstable rust custom test framework test runner
pub fn kernel_test_runner(tests: &[&dyn Fn()]) {
    println!("Kernel integration test start...");
    println!("Running {} tests", tests.len());
    for test in tests {
        test();
    }
    println!("Kernel integration test end.");
}

#[no_mangle]
fn main() -> i32 {
    println!("Hello, BlueKernel!");

    let memory_info = allocator::memory_info();
    println!("Kernel memory statistics: ");
    println!("Total memory: {} bytes.", memory_info.total);
    println!("Used memory: {} bytes.", memory_info.used);
    println!("Max used memory: {} bytes.", memory_info.max_used);

    // Unstable rust custom test framework tests entry.
    kernel_test_main();

    #[cfg(coverage)]
    blueos::coverage::write_coverage_data();
    0
}
