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

#![cfg_attr(not(feature = "std"), no_std)]

extern crate blueos;
use core::alloc::{GlobalAlloc, Layout};

#[cfg(not(feature = "std"))]
struct PosixAllocator;

#[cfg(not(feature = "std"))]
unsafe impl GlobalAlloc for PosixAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        blueos::allocator::malloc_align(layout.size(), layout.align())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        blueos::allocator::free_align(ptr, layout.align())
    }
}

// rust-std has its own allocator and panic_handler.
#[cfg(not(feature = "std"))]
#[global_allocator]
static GLOBAL: PosixAllocator = PosixAllocator;

#[cfg(any(
    target_arch = "riscv32",
    target_arch = "riscv64",
    target_arch = "aarch64"
))]
fn trace_stack() {
    use core::ffi::c_void;
    use unwinding::abi::*;
    #[derive(Default)]
    struct StackInfo {
        depth: usize,
    };
    extern "C" fn unwinder_callback(
        unwind_ctx: &UnwindContext<'_>,
        arg: *mut c_void,
    ) -> UnwindReasonCode {
        let info = unsafe { &mut *(arg as *mut StackInfo) };
        semihosting::eprintln!(
            "{:4}:{:#19x} - <unknown>",
            info.depth,
            _Unwind_GetIP(unwind_ctx)
        );
        info.depth += 1;
        UnwindReasonCode::NO_REASON
    }
    let mut info = StackInfo::default();
    _Unwind_Backtrace(unwinder_callback, &mut info as *mut _ as _);
}

#[cfg(not(feature = "std"))]
#[panic_handler]
fn oops(info: &core::panic::PanicInfo) -> ! {
    // Enable semihosting on qemu boards.
    #[cfg(any(
        target_board = "qemu_mps2_an385",
        target_board = "qemu_mps3_an547",
        target_board = "qemu_riscv32",
        target_board = "qemu_riscv64",
        target_board = "qemu_virt64_aarch64",
    ))]
    {
        semihosting::println!("{}", info);
        semihosting::println!("{}", info.message());
        #[cfg(any(
            target_arch = "riscv32",
            target_arch = "riscv64",
            target_arch = "aarch64"
        ))]
        trace_stack();
    }
    loop {}
}

#[used]
#[link_section = ".bk_app_array"]
static INIT: extern "C" fn() = init;

extern "C" fn init() {
    #[cfg(feature = "std")]
    {
        extern "C" {
            fn __librs_start_main();
        }
        unsafe { __librs_start_main() };
    }

    #[cfg(not(feature = "std"))]
    {
        extern "C" {
            fn main() -> i32;
        }
        unsafe { main() };
    }
}
