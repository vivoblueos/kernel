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

#[cfg(not(feature = "std"))]
#[panic_handler]
fn oops(info: &core::panic::PanicInfo) -> ! {
    #[cfg(debug)]
    semihosting::println!("{}", info);
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
