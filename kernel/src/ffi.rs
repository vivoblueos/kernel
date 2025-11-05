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

use crate::allocator;
use core::ffi::c_int;

#[coverage(off)]
#[no_mangle]
pub extern "C" fn disable_local_irq_save() -> usize {
    crate::arch::disable_local_irq_save()
}

#[coverage(off)]
#[no_mangle]
pub extern "C" fn enable_local_irq_restore(val: usize) {
    crate::arch::enable_local_irq_restore(val)
}

#[coverage(off)]
#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn __aeabi_memclr8(s: *mut u8, n: usize) -> *mut u8 {
    let mut i = 0;
    for i in 0..n {
        s.add(i).write(0u8);
    }
    s
}

// TODO: Implement an edidx unwinder for BlueOS.
#[coverage(off)]
#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn __aeabi_unwind_cpp_pr0() {}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn posix_memalign(ptr: *mut *mut u8, align: usize, size: usize) -> c_int {
    let addr = allocator::malloc_align(size, align);
    if addr.is_null() {
        return -1;
    }
    unsafe { *ptr = addr };
    0
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn free(ptr: *mut u8) {
    allocator::free(ptr)
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn malloc(size: usize) -> *mut u8 {
    allocator::malloc(size)
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn memalign(align: usize, size: usize) -> *mut u8 {
    allocator::malloc_align(size, align)
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn calloc(count: usize, size: usize) -> *mut u8 {
    allocator::calloc(count, size)
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn realloc(ptr: *mut u8, newsize: usize) -> *mut u8 {
    allocator::realloc(ptr, newsize)
}
