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

#![no_std]
#![cfg_attr(test, feature(custom_test_frameworks))]
#![cfg_attr(test, test_runner(tests::run_tests))]
#![cfg_attr(test, reexport_test_harness_main = "test_main")]
#![cfg_attr(test, no_main)]
#![feature(const_trait_impl)]
#![feature(negative_impls)]

extern crate alloc;

pub mod mempool;

#[cfg(test)]
mod tests {
    // FIXME: We have too many duplicated code setting up unittest environment.
    use super::*;
    use blueos::{allocator::KernelAllocator, thread};

    #[global_allocator]
    static ALLOCATOR: KernelAllocator = KernelAllocator;

    #[panic_handler]
    fn oops(info: &core::panic::PanicInfo<'_>) -> ! {
        let _dig = blueos::support::DisableInterruptGuard::new();
        semihosting::println!("{}", info);
        semihosting::println!("Oops: {}", info.message());
        loop {}
    }

    #[used]
    #[link_section = ".bk_app_array"]
    static INIT_TEST: extern "C" fn() = init_test;

    extern "C" fn init_test() {
        thread::Builder::new(thread::Entry::C(test_entry)).start();
    }

    extern "C" fn test_entry() {
        test_main();
    }

    pub(crate) fn run_tests(tests: &[&dyn Fn()]) {
        semihosting::println!("BlueOS adapter unittest started");
        for test in tests {
            test();
        }
        semihosting::println!("BlueOS adapter unittest ended");
    }
}
