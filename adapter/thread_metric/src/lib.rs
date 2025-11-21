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
    thread::{READY, SUSPENDED},
};
use blueos_kconfig::TICKS_PER_SECOND;
use core::mem::MaybeUninit;
use libc::c_int;

extern "C" {
    fn tm_main();
}

#[used]
#[link_section = ".bk_app_array"]
static TM_MAIN: unsafe extern "C" fn() = tm_main;
const TM_SUCCESS: c_int = 0;
const TM_ERROR: c_int = 1;

const MAX_THREADS: usize = 16;
static mut TM_THREADS: [MaybeUninit<ThreadNode>; MAX_THREADS] =
    [MaybeUninit::zeroed(); MAX_THREADS];

#[no_mangle]
pub extern "C" fn tm_initialize(test_initialization_function: extern "C" fn()) {
    test_initialization_function()
}

#[no_mangle]
pub extern "C" fn tm_thread_create(
    thread_id: c_int,
    priority: c_int,
    entry: extern "C" fn(),
) -> c_int {
    let builder = thread::Builder::new(Entry::C(entry));
    let t = builder.set_priority(priority).build();
    unsafe {
        TM_THREADS[thread_id as usize].write(t);
    }
    TM_SUCCESS
}

#[no_mangle]
pub extern "C" fn tm_thread_resume(thread_id: c_int) -> c_int {
    let t = unsafe { TM_THREADS[thread_id as usize].asseum_init_ref().clone() };
    if scheduler::queue_ready_thread(t.state(), t) {
        return TM_SUCCESS;
    }
    TM_ERROR
}

#[no_mangle]
pub extern "C" fn tm_thread_suspend(thread_id: c_int) -> c_int {
    let t = unsafe { TM_THREADS[thread_id as usize].asseum_init_ref() };
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
