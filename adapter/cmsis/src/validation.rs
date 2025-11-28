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
#![cfg_attr(test, test_runner(tests::validation_test_runner))]
#![cfg_attr(test, reexport_test_harness_main = "validation_test_main")]
#![cfg_attr(test, no_main)]
#![feature(c_size_t)]
#![feature(const_trait_impl)]
#![feature(negative_impls)]
#![feature(linkage)]

extern crate alloc;

pub mod bridge_utils;
pub mod common_objects;
use alloc::slice;
#[cfg(cmsis_rtos1_adapter)]
pub mod os1;
#[cfg(cmsis_rtos2_adapter)]
pub mod os2;
pub use blueos::types::Arc;
pub const MAX_NAME_LEN: usize = 16;
pub mod uart;

#[cfg(test)]
mod tests {
    use super::*;
    use blueos::{
        allocator::{memory_info, KernelAllocator},
        arch, scheduler,
        thread::{Builder, Entry, Thread, ThreadNode},
    };

    #[global_allocator]
    static ALLOCATOR: KernelAllocator = KernelAllocator;

    #[used]
    #[link_section = ".bk_app_array"]
    static INIT_TEST: extern "C" fn() = init_test;

    #[inline(never)]
    pub fn validation_test_runner(tests: &[&dyn Fn()]) {
        let t = scheduler::current_thread();
        semihosting::println!("cmsis_rv2 unittest started");

        unsafe { cmsis_rv2() };
        semihosting::println!("cmsis_rv2 unittest finished");
    }
    // wrapper functions for cmsis_rv2, avoid rc count problem
    #[no_mangle]
    pub unsafe extern "C" fn report_before_rv2() {
        let t = scheduler::current_thread();
        semihosting::println!(
            "Before cmsis_rv2, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t) - 1,
            memory_info(),
            arch::current_sp()
        );
    }
    // wrapper functions for cmsis_rv2, avoid rc count problem
    #[no_mangle]
    pub unsafe extern "C" fn report_after_rv2() {
        let t = scheduler::current_thread();
        semihosting::println!(
            "After cmsis_rv2, thread 0x{:x}, rc: {}, heap status: {:?}, sp: 0x{:x}",
            Thread::id(&t),
            ThreadNode::strong_count(&t) - 1,
            memory_info(),
            arch::current_sp()
        );
    }
    // copy from librs, cmsis_rv2 need an c library in fact
    #[no_mangle]
    unsafe extern "C" fn strncmp(
        s1: *const core::ffi::c_char,
        s2: *const core::ffi::c_char,
        n: core::ffi::c_size_t,
    ) -> core::ffi::c_int {
        let s1 = slice::from_raw_parts(s1 as *const core::ffi::c_uchar, n);
        let s2 = slice::from_raw_parts(s2 as *const core::ffi::c_uchar, n);

        for (&a, &b) in s1.iter().zip(s2.iter()) {
            let val = (a as core::ffi::c_int) - (b as core::ffi::c_int);
            if a != b || a == 0 {
                return val;
            }
        }

        0
    }

    use cortex_m::interrupt::InterruptNumber;

    // copy from kernel/src/arch/arm/irq.rs
    // used for rv2 ISR context api tests
    #[derive(Debug, Copy, Clone)]
    #[repr(transparent)]
    pub struct IrqNumber(u16);
    impl IrqNumber {
        #[inline]
        pub const fn new(number: u16) -> Self {
            Self(number)
        }
    }
    // SAFETY: get the number of the interrupt is safe
    unsafe impl InterruptNumber for IrqNumber {
        #[inline]
        fn number(self) -> u16 {
            self.0
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn NVIC_SetPriority(irq: u16, priority: u8) {
        cortex_m::Peripherals::steal()
            .NVIC
            .set_priority(IrqNumber::new(irq), priority);
    }
    #[no_mangle]
    pub unsafe extern "C" fn NVIC_EnableIRQ(irq: u16) {
        cortex_m::peripheral::NVIC::unmask(IrqNumber::new(irq));
    }

    #[no_mangle]
    pub unsafe extern "C" fn NVIC_DisableIRQ(irq: u16) {
        cortex_m::peripheral::NVIC::mask(IrqNumber::new(irq));
    }

    #[no_mangle]
    pub unsafe extern "C" fn NVIC_GetPendingIRQ(irq: u16) -> bool {
        cortex_m::peripheral::NVIC::is_pending(IrqNumber::new(irq))
    }

    #[no_mangle]
    pub unsafe extern "C" fn NVIC_SetPendingIRQ(irq: u16) {
        cortex_m::peripheral::NVIC::pend(IrqNumber::new(irq));
    }

    #[no_mangle]
    pub unsafe extern "C" fn strcmp(
        s1: *const core::ffi::c_char,
        s2: *const core::ffi::c_char,
    ) -> core::ffi::c_int {
        strncmp(s1, s2, isize::MAX as core::ffi::c_size_t)
    }

    unsafe extern "C" {
        #[link_name = "cmsis_rv2"]
        #[no_mangle]
        fn cmsis_rv2();
    }
    extern "C" fn init_test() {
        validation_test_main();
    }
    #[no_mangle]
    extern "C" fn stdout_putchar(c: i32) {
        use semihosting::io::Write;
        semihosting::io::stdout()
            .expect("Failed to get stdout")
            .write_all(&[c as u8]);
    }

    #[no_mangle]
    extern "C" fn stdout_flush() {
        use semihosting::io::Write;
        semihosting::io::stdout()
            .expect("Failed to get stdout")
            .flush()
            .expect("Failed to flush stdout");
    }

    #[panic_handler]
    fn oops(info: &core::panic::PanicInfo<'_>) -> ! {
        let _dig = blueos::support::DisableInterruptGuard::new();
        semihosting::println!("{}", info);
        semihosting::println!("Oops: {}", info.message());
        loop {}
    }
}
