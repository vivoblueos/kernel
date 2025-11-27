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

#![no_std]

use blueos::{
    scheduler, thread,
    thread::{Entry, Thread, ThreadNode, CREATED, READY, RUNNING, SUSPENDED},
    types::{Arc, ThreadPriority},
};
use blueos_kconfig::TICKS_PER_SECOND;
use core::mem::MaybeUninit;
use libc::c_int;

const TM_SUCCESS: c_int = 0;
const TM_ERROR: c_int = 1;

const MAX_THREADS: usize = 16;
static mut TM_THREADS: [MaybeUninit<ThreadNode>; MAX_THREADS] =
    [const { MaybeUninit::zeroed() }; MAX_THREADS];

#[no_mangle]
pub extern "C" fn tm_initialize(test_initialization_function: extern "C" fn()) {
    // This thread is responsible to start worker threads. Make it the highest priority
    // so that all worker threads are created before running.
    {
        let this_thread = blueos::scheduler::current_thread();
        let mut w = this_thread.lock();
        w.set_origin_priority(0);
        w.set_priority(0);
    }
    test_initialization_function()
}

extern "C" fn tm_thread_start(arg: *mut core::ffi::c_void) {
    librs::pthread::register_my_tcb();
    let entry: extern "C" fn() = unsafe { core::mem::transmute(arg) };
    entry();
}

#[no_mangle]
pub extern "C" fn tm_thread_create(
    thread_id: c_int,
    priority: c_int,
    entry: extern "C" fn(),
) -> c_int {
    let builder = thread::Builder::new(Entry::Posix(
        tm_thread_start,
        entry as *mut core::ffi::c_void,
    ));
    let t = builder.set_priority(priority as ThreadPriority).build();
    unsafe {
        TM_THREADS[thread_id as usize].write(t);
    }
    TM_SUCCESS
}

#[no_mangle]
pub extern "C" fn tm_thread_resume(thread_id: c_int) -> c_int {
    let t = unsafe { TM_THREADS[thread_id as usize].assume_init_ref().clone() };
    let this_thread = scheduler::current_thread();
    // Resuming myself always succeeds.
    if Thread::id(&this_thread) == Thread::id(&t) {
        return TM_SUCCESS;
    }
    if scheduler::queue_ready_thread(SUSPENDED, t.clone())
        || scheduler::queue_ready_thread(CREATED, t)
    {
        scheduler::relinquish_me();
        return TM_SUCCESS;
    }
    TM_ERROR
}

#[no_mangle]
pub extern "C" fn tm_thread_suspend(thread_id: c_int) -> c_int {
    let t = unsafe { TM_THREADS[thread_id as usize].assume_init_ref() };
    let this_thread = scheduler::current_thread();
    // I'm suspending myself.
    if Thread::id(&this_thread) == Thread::id(&t) {
        scheduler::suspend_me();
        return TM_SUCCESS;
    }
    if scheduler::remove_from_ready_queue(t) {
        t.transfer_state(READY, SUSPENDED);
        return TM_SUCCESS;
    }
    TM_ERROR
}

#[no_mangle]
pub extern "C" fn tm_thread_relinquish() {
    scheduler::relinquish_me()
}

#[no_mangle]
pub extern "C" fn tm_thread_sleep(secs: c_int) {
    scheduler::suspend_me_for(TICKS_PER_SECOND * secs as usize);
}
