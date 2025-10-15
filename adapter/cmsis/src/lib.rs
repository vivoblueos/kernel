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

#![allow(non_snake_case)]
#![no_std]
#![cfg_attr(test, feature(custom_test_frameworks))]
#![cfg_attr(test, test_runner(tests::adapter_test_runner))]
#![cfg_attr(test, reexport_test_harness_main = "adapter_test_main")]
#![cfg_attr(test, no_main)]

extern crate alloc;
pub mod bridge_utils;
pub mod common_objects;
pub use blueos::types::Arc;
#[cfg(cmsis_rtos1_adapter)]
pub mod os1;
#[cfg(cmsis_rtos2_adapter)]
pub mod os2;

pub const MAX_NAME_LEN: usize = 8;

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::{
        allocator::KernelAllocator,
        arch, scheduler,
        thread::{Builder, Entry, Thread, ThreadNode},
    };

    #[global_allocator]
    static ALLOCATOR: KernelAllocator = KernelAllocator;

    #[used]
    #[link_section = ".bk_app_array"]
    static INIT_TEST: extern "C" fn() = init_test;

    #[inline(never)]
    pub fn adapter_test_runner(tests: &[&dyn Fn()]) {
        let t = scheduler::current_thread();
        semihosting::println!("CMSIS adapter unittest started");
        semihosting::println!("Running {} tests", tests.len());
        semihosting::println!(
            "Before test, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t),
            ALLOCATOR.memory_info(),
            arch::current_sp(),
        );
        for test in tests {
            test();
        }
        semihosting::println!(
            "After test, thread 0x{:x}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ALLOCATOR.memory_info(),
            arch::current_sp(),
        );
        semihosting::println!("CMSIS adapter unittest ended");

        #[cfg(coverage)]
        blueos::coverage::write_coverage_data();
    }

    extern "C" fn test_main() {
        adapter_test_main();
    }

    extern "C" fn init_test() {
        semihosting::println!("create test thread");
        let t = Builder::new(Entry::C(test_main)).start();
    }

    #[panic_handler]
    fn oops(info: &core::panic::PanicInfo<'_>) -> ! {
        let _dig = blueos::support::DisableInterruptGuard::new();
        semihosting::println!("{}", info);
        semihosting::println!("Oops: {}", info.message());
        loop {}
    }
}
