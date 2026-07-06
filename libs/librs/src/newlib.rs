// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

use core::alloc::{GlobalAlloc, Layout};
use libc::{c_int, c_void};

#[macro_use]
extern crate alloc;
pub mod retarget;
pub mod syncs;
pub mod syscalls;

#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(non_upper_case_globals)]
#[allow(dead_code)]
mod reent_types {
    include!(env!("BINDGEN_DIR"));
}
pub use reent_types::*;

struct PosixAllocator;
unsafe impl GlobalAlloc for PosixAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        blueos::allocator::malloc_align(layout.size(), layout.align())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        blueos::allocator::free_align(ptr, layout.align())
    }
}

#[global_allocator]
static GLOBAL: PosixAllocator = PosixAllocator;

#[panic_handler]
fn oops(info: &core::panic::PanicInfo) -> ! {
    semihosting::println!("{}", info.message());
    {
        semihosting::println!("---- Begin stack unwinding ----");
        unsafe {
            unwind_use_libgcc();
        }
        semihosting::println!("---- Ended stack unwinding ----");
    }
    loop {}
}

// workaround
#[no_mangle]
pub unsafe extern "C" fn _fini() {}

#[no_mangle]
pub static __dso_handle: usize = 0;

const _UVRSC_CORE: u32 = 0;
const _UVRSD_UINT32: u32 = 0;

extern "C" {
    fn _Unwind_Backtrace(
        callback: unsafe extern "C" fn(*mut c_void, *mut c_void) -> c_int,
        arg: *mut c_void,
    ) -> c_int;

    fn _Unwind_VRS_Get(
        context: *mut c_void,
        regclass: u32,
        regno: u32,
        representation: u32,
        valuep: *mut u32,
    ) -> u32;
}
// TODO: support unwind in panic FAULT_HANDLER
unsafe fn unwind_use_libgcc() {
    // TODO: add signal support report backtrace?
    unsafe extern "C" fn unwinder_callback(unwind_ctx: *mut c_void, arg: *mut c_void) -> c_int {
        0
    }

    _Unwind_Backtrace(unwinder_callback, core::ptr::null_mut());
}
