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
#![feature(thread_local)]
#![feature(rustc_private)]
#![feature(fn_align)]

extern crate alloc;
use alloc::{boxed::Box, ffi::CString, format, vec::Vec};
use core::{
    alloc::{GlobalAlloc, Layout},
    ffi::CStr,
    ptr,
};
use libc::c_void;

#[cfg(coverage)]
use common_cov;

#[thread_local]
static mut ID: i32 = 42;

// Should be put in .bss section.
static mut LARGE_ARRAY: [u8; 1024] = [0u8; 1024];

struct PosixAllocator;

unsafe impl GlobalAlloc for PosixAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() == 0 {
            return ptr::null_mut();
        }

        let mut mem_ptr: *mut c_void = ptr::null_mut();
        let align = layout.align();
        let size = layout.size();

        let result =
            librs::stdlib::malloc::posix_memalign(&mut mem_ptr as *mut *mut c_void, align, size);

        if result == 0 {
            mem_ptr as *mut u8
        } else {
            ptr::null_mut()
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        if !ptr.is_null() {
            librs::stdlib::malloc::free(ptr as *mut c_void);
        }
    }
}

#[global_allocator]
static GLOBAL: PosixAllocator = PosixAllocator;

#[panic_handler]
fn panic(info: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

#[no_mangle]
#[repr(align(8))]
pub extern "C" fn _start() {
    // FIXME: Generally we need toolchains able to build static-pie,
    // thus we have dynamic relocation entres to relocate .got
    // entries. GNU's ld targeted bare-metal targets failed to
    // generate static-pie ELF. See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=106356.
    // That's to say, currently the ELF file
    // is of type EXEC, however we need it to be DYN.
    // Also libcore, liballoc should be built with -fpic
    // enabled. Currently non-riscv targets just passes the test by
    // luck.
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    assert_eq!(main(42), 42);
}

#[no_mangle]
#[inline(never)]
extern "C" fn main(argc: i32) -> i32 {
    // FIXME: Current librs::stdio::puts impl makes this program hangs forever.
    unsafe {
        let b = Box::new(ID);
        let mut v = Vec::new();
        v.extend_from_slice(&[ID; 128]);
        LARGE_ARRAY[argc as usize] = ID as u8;
        assert_eq!(*b as u8, LARGE_ARRAY[argc as usize]);

        #[cfg(coverage)]
        common_cov::write_coverage_data();

        LARGE_ARRAY[argc as usize] as i32
    }
}
