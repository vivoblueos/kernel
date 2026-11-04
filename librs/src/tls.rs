// This file is Rust impl of LLVM's emutls.c.
//===---------- emutls.c - Implements __emutls_get_address ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

use crate::{
    pthread::{pthread_getspecific, pthread_key_create, pthread_setspecific},
    stdlib::malloc::{free, posix_memalign},
    string::{memcpy, memset},
};
use alloc::{boxed::Box, vec::Vec};
use core::{
    ffi::c_void,
    ops::Add,
    sync::atomic::{AtomicUsize, Ordering},
};
use libc::pthread_key_t;
use spin::{once::Once, RwLock};

#[derive(Default)]
struct EmutlsAddressArray {
    data: Vec<*mut u8>,
}

#[repr(C)]
struct EmutlsControl {
    size: usize,
    align: usize,
    object: EmutlsObject,
    value: *mut c_void,
}

#[repr(C)]
union EmutlsObject {
    index: usize,
    address: *mut c_void,
}

static EMUTLS_NUM_OBJECT: RwLock<usize> = RwLock::new(0);
static EMUTLS_PTHREAD_KEY: Once<pthread_key_t> = Once::new();

extern "C" fn emutls_key_destructor(arg: *mut c_void) {
    let array_ptr = arg as *mut EmutlsAddressArray;
    let mut boxed_array = unsafe { Box::from_raw(array_ptr) };
    while let Some(data) = boxed_array.data.pop() {
        unsafe { free(data as *mut libc::c_void) };
    }
    drop(boxed_array);
}

fn get_or_create_emutls_key() -> &'static pthread_key_t {
    EMUTLS_PTHREAD_KEY.call_once(|| {
        let mut key: pthread_key_t = 0;
        if pthread_key_create(&mut key as *mut pthread_key_t, Some(emutls_key_destructor)) != 0 {
            panic!("Unable to create pthread key for emutls")
        }
        key
    })
}

fn get_or_create_specific<'a>() -> &'a mut EmutlsAddressArray {
    let key = *get_or_create_emutls_key();
    unsafe {
        let ptr = pthread_getspecific(key);
        if ptr.is_null() {
            let boxed_array = Box::new(EmutlsAddressArray::default());
            // Let's leak this array and then we'll deallocate it via `Box::from_raw`.
            let leaked_ptr = Box::into_raw(boxed_array);
            let rc = pthread_setspecific(key, leaked_ptr as *const c_void);
            assert_eq!(rc, 0);
            assert_eq!(leaked_ptr as *mut c_void, pthread_getspecific(key));
            &mut *leaked_ptr
        } else {
            &mut *(ptr as *mut EmutlsAddressArray)
        }
    }
}

fn get_address_array<'a>(index: usize) -> &'a mut EmutlsAddressArray {
    let array = get_or_create_specific();
    if index >= array.data.len() {
        array.data.resize(index + 1, core::ptr::null_mut());
    }
    array
}

fn get_index(control: &mut EmutlsControl) -> usize {
    let atomic_index = unsafe { AtomicUsize::from_mut(&mut control.object.index) };
    // Control is 1-indexed.
    let mut index = atomic_index.load(Ordering::Acquire);
    if index == 0 {
        get_or_create_emutls_key();
        let mut write = EMUTLS_NUM_OBJECT.write();
        index = atomic_index.load(Ordering::Acquire);
        if index == 0 {
            *write = write.add(1);
            index = *write;
            atomic_index.store(index, Ordering::Release);
        }
    }
    index
}

fn allocate_object(ctrl: &EmutlsControl) -> *mut u8 {
    let size = ctrl.size;
    let align = ctrl.align;
    let mut base: *mut u8 = core::ptr::null_mut();
    unsafe {
        // We'll deallocate it via `free()`.
        let rc = posix_memalign(
            &mut base as *mut *mut u8 as *mut *mut libc::c_void,
            align,
            size,
        );
        assert_eq!(rc, 0);
        assert!(!base.is_null());
        if ctrl.value.is_null() {
            memset(base as *mut c_void, 0, size);
        } else {
            memcpy(base as *mut c_void, ctrl.value, size);
        }
    }
    base
}

#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn __emutls_get_address(ptr: *mut c_void) -> *mut c_void {
    let ctrl = unsafe { &mut *ptr.cast::<EmutlsControl>() };
    let mut index = get_index(ctrl);
    // Array is 0-indexed.
    index -= 1;
    let array = get_address_array(index);
    if array.data[index].is_null() {
        array.data[index] = allocate_object(ctrl);
    }
    array.data[index] as *mut c_void
}
