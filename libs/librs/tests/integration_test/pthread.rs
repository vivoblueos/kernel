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

extern crate alloc;
use alloc::vec::Vec;
use blueos_test_macro::{only_test, test};
use core::{
    cell::{Cell, RefCell},
    ffi::c_void,
    intrinsics::transmute,
    mem::{align_of, size_of, MaybeUninit},
    sync::atomic::{AtomicI8, AtomicUsize, Ordering},
};
use libc::{
    clockid_t, pthread_attr_t, pthread_cond_t, pthread_condattr_t, pthread_key_t, pthread_mutex_t,
    pthread_mutexattr_t, pthread_self, pthread_t, EDEADLK, EINVAL, ESRCH,
};
use librs::{
    pthread::*,
    stdlib::malloc::{free, posix_memalign},
    sync::{
        cond::{Cond, CondAttr},
        mutex::{Mutex, MutexAttr},
        waitval::Waitval,
    },
};

extern "C" fn mutex_lock_unlock(arg: *mut c_void) -> *mut c_void {
    let mutex = arg.cast::<pthread_mutex_t>();
    assert_eq!(pthread_mutex_lock(mutex), 0);
    assert_eq!(pthread_mutex_unlock(mutex), 0);
    core::ptr::null_mut()
}

#[test]
fn test_single_thread_mutex() {
    let mut mutex: pthread_mutex_t = unsafe { MaybeUninit::zeroed().assume_init() };
    pthread_mutex_init(&mut mutex as *mut _, core::ptr::null());
    unsafe {
        mutex_lock_unlock(transmute::<*mut pthread_mutex_t, *mut c_void>(
            &mut mutex as *mut pthread_mutex_t,
        ));
    }
}

#[test]
fn test_multi_thread_mutex() {
    let mut mutex: pthread_mutex_t = unsafe { MaybeUninit::zeroed().assume_init() };
    #[cfg(target_pointer_width = "32")]
    let num_threads = 4;
    #[cfg(target_pointer_width = "64")]
    let num_threads = 32;
    let mut threads = Vec::new();
    for _ in 0..num_threads {
        let mut t: pthread_t = 0;
        let rc = pthread_create(
            &mut t as *mut pthread_t,
            core::ptr::null_mut(),
            mutex_lock_unlock,
            &mut mutex as *mut pthread_mutex_t as *mut c_void,
        );
        assert_eq!(rc, 0);
        threads.push(t);
    }
    for t in threads {
        assert_eq!(pthread_join(t, core::ptr::null_mut()), 0);
    }
}

struct Waiter(*mut pthread_cond_t, *mut pthread_mutex_t, bool);

#[allow(clippy::while_immutable_condition)]
extern "C" fn cond_wait(arg: *mut c_void) -> *mut c_void {
    let waiter = unsafe { &*arg.cast::<Waiter>() };
    assert_eq!(pthread_mutex_lock(waiter.1), 0);
    while !waiter.2 {
        assert_eq!(pthread_cond_wait(waiter.0, waiter.1), 0);
    }
    assert_eq!(pthread_mutex_unlock(waiter.1), 0);
    core::ptr::null_mut()
}

#[test]
fn test_multi_thread_cond() {
    let mut cond: pthread_cond_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let condattr: CondAttr = CondAttr::default();
    pthread_cond_init(
        &mut cond as *mut pthread_cond_t,
        &condattr as *const CondAttr as *const pthread_condattr_t,
    );
    let mut mutex: pthread_mutex_t = unsafe { MaybeUninit::zeroed().assume_init() };
    let mut waiter = Waiter(
        &mut cond as *mut pthread_cond_t,
        &mut mutex as *mut pthread_mutex_t,
        false,
    );
    let mut threads = Vec::new();
    #[cfg(target_pointer_width = "32")]
    let num_threads = 4;
    #[cfg(target_pointer_width = "64")]
    let num_threads = 32;
    for _ in 0..num_threads {
        let mut t: pthread_t = 0;
        let rc = pthread_create(
            &mut t as *mut pthread_t,
            core::ptr::null_mut(),
            cond_wait,
            &mut waiter as *mut Waiter as *mut c_void,
        );
        assert_eq!(rc, 0);
        threads.push(t);
    }
    assert_eq!(pthread_mutex_lock(waiter.1), 0);
    waiter.2 = true;
    assert_eq!(pthread_cond_signal(waiter.0), 0);
    assert_eq!(pthread_mutex_unlock(waiter.1), 0);
    for t in threads {
        assert_eq!(pthread_join(t, core::ptr::null_mut()), 0);
    }
}

#[thread_local]
static THREAD_LOCAL_CHECK: Cell<usize> = Cell::new(42);

#[thread_local]
static LOCAL_VEC: RefCell<Vec<i32>> = RefCell::new(Vec::new());

#[test]
fn test_complex_thread_local() {
    fn is_prime(n: i32) -> bool {
        let mut i = 2;
        while i * i <= n {
            if n % i == 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    for i in 2..1024 {
        if is_prime(i) {
            LOCAL_VEC.borrow_mut().push(i);
        }
    }
}

extern "C" fn increase_counter(arg: *mut c_void) -> *mut c_void {
    let counter: *mut AtomicUsize = unsafe { transmute(arg) };
    let old = unsafe { &*counter }.fetch_add(1, Ordering::Release);
    core::ptr::null_mut()
}

#[test]
fn test_pthread_create_and_join() {
    #[cfg(target_pointer_width = "32")]
    let num_threads = 4;
    #[cfg(target_pointer_width = "64")]
    let num_threads = 32;
    let mut threads = Vec::new();
    let mut counter = AtomicUsize::new(0);
    for _ in 0..num_threads {
        let mut t: pthread_t = 0;
        let arg: *mut c_void = &mut counter as *mut AtomicUsize as *mut c_void;
        let rc = pthread_create(
            &mut t as *mut pthread_t,
            core::ptr::null(),
            increase_counter,
            arg,
        );
        assert_eq!(rc, 0);
        threads.push(t);
    }
    let mut num_joined = 0;
    for t in threads {
        assert_eq!(pthread_join(t, core::ptr::null_mut()), 0);
        num_joined += 1;
    }
    assert_eq!(num_threads, num_joined);
    assert_eq!(counter.load(Ordering::Acquire), num_threads);
}

static DETACH_TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

extern "C" fn detach_and_increase_counter(arg: *mut c_void) -> *mut c_void {
    DETACH_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    core::ptr::null_mut()
}

#[test]
fn test_pthread_create_and_detach() {
    #[cfg(target_pointer_width = "32")]
    let num_threads = 4;
    #[cfg(target_pointer_width = "64")]
    let num_threads = 32;
    let mut threads = Vec::new();
    let mut counter = AtomicUsize::new(0);
    let mut num_detached = 0;
    for _ in 0..num_threads {
        let mut t: pthread_t = 0;
        let arg: *mut c_void = &mut counter as *mut AtomicUsize as *mut c_void;
        let rc = pthread_create(
            &mut t as *mut pthread_t,
            core::ptr::null(),
            detach_and_increase_counter,
            arg,
        );
        assert_eq!(rc, 0);
        let ret = pthread_detach(t);
        // If ret == libc::ESRCH, the thread might be detached and
        // then exited.
        if ret == 0 || ret == libc::ESRCH {
            num_detached += 1;
            continue;
        }
        threads.push(t);
    }
    let mut num_joined = 0;
    for t in threads {
        assert_eq!(pthread_join(t, core::ptr::null_mut()), 0);
        num_joined += 1;
    }
    assert_eq!(num_joined + num_detached, num_threads);
}

#[test]
fn test_thread_local() {
    assert_eq!(THREAD_LOCAL_CHECK.get(), 42);
}
