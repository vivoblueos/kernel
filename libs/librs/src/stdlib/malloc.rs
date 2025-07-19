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

// FIXME: We are using kernel's allocator currently. Formally, we should use mmap to implement malloc.
use blueos_header::syscalls::NR::{AllocMem, FreeMem};
use blueos_scal::bk_syscall;
use libc::{c_int, c_void, size_t, ENOMEM};

#[no_mangle]
pub unsafe extern "C" fn posix_memalign(
    ptr: *mut *mut c_void,
    align: size_t,
    size: size_t,
) -> c_int {
    let rc = bk_syscall!(AllocMem, ptr, size, align);
    if rc != 0 {
        return ENOMEM;
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    debug_assert_eq!(bk_syscall!(FreeMem, ptr), 0);
}

#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    let mut ptr: *mut c_void = core::ptr::null_mut();
    let rc = posix_memalign(
        &mut ptr as *mut *mut c_void,
        core::mem::size_of::<usize>(),
        size,
    );
    if rc != 0 {
        return core::ptr::null_mut();
    }
    ptr
}
