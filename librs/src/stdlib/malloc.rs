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
use blueos_header::syscalls::NR::{AllocMem, FreeMem, ReallocMem};
use blueos_scal::bk_syscall;
use libc::{c_int, c_void, size_t, EINVAL, ENOMEM};

fn set_errno(value: c_int) {
    crate::errno::ERRNO.set(value);
}

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
    bk_syscall!(FreeMem, ptr);
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

/*
 * realloc cannot be composed from AllocMem and FreeMem: nothing outside the
 * allocator knows the size of the block being resized, so there is no way to
 * copy the right number of bytes. It gets a syscall of its own instead
 * (ReallocMem), which is also what makes the Issue 8 reallocarray() below
 * expressible at all.
 */
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: size_t) -> *mut c_void {
    let mut new_ptr: *mut c_void = core::ptr::null_mut();
    let rc = bk_syscall!(ReallocMem, &mut new_ptr as *mut *mut c_void, ptr, size);
    if rc != 0 {
        set_errno(ENOMEM);
        return core::ptr::null_mut();
    }
    new_ptr
}

#[no_mangle]
pub unsafe extern "C" fn calloc(nmemb: size_t, size: size_t) -> *mut c_void {
    let total = match nmemb.checked_mul(size) {
        Some(total) => total,
        None => {
            set_errno(ENOMEM);
            return core::ptr::null_mut();
        }
    };
    let ptr = malloc(total);
    if ptr.is_null() {
        set_errno(ENOMEM);
        return core::ptr::null_mut();
    }
    core::ptr::write_bytes(ptr as *mut u8, 0, total);
    ptr
}

/*
 * Issue 8. Defined here rather than left to the C library because newlib's
 * aligned_alloc() reaches memalign(), which lives in the same object as
 * newlib's sbrk-based malloc; linking it would put a second allocator over a
 * second heap next to the kernel's.
 */
#[no_mangle]
pub unsafe extern "C" fn aligned_alloc(alignment: size_t, size: size_t) -> *mut c_void {
    // Issue 8: a non-power-of-two alignment is EINVAL, not a best effort.
    if alignment == 0 || !alignment.is_power_of_two() {
        set_errno(EINVAL);
        return core::ptr::null_mut();
    }
    // Anything below pointer alignment is already satisfied by the allocator.
    let align = if alignment < core::mem::size_of::<usize>() {
        core::mem::size_of::<usize>()
    } else {
        alignment
    };
    let mut ptr: *mut c_void = core::ptr::null_mut();
    if bk_syscall!(AllocMem, &mut ptr as *mut *mut c_void, size, align) != 0 {
        set_errno(ENOMEM);
        return core::ptr::null_mut();
    }
    ptr
}

/*
 * Issue 8. The whole point of reallocarray over realloc is that the
 * multiplication is checked: an overflowing product fails here instead of
 * turning into a small allocation the caller then overruns.
 */
#[no_mangle]
pub unsafe extern "C" fn reallocarray(
    ptr: *mut c_void,
    nmemb: size_t,
    size: size_t,
) -> *mut c_void {
    match nmemb.checked_mul(size) {
        Some(total) => realloc(ptr, total),
        None => {
            set_errno(ENOMEM);
            core::ptr::null_mut()
        }
    }
}
