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
use crate::{
    arch,
    config::MAX_THREAD_PRIORITY,
    scheduler::RUNNING_THREADS,
    support,
    thread::{self, Entry, SystemThreadStorage, Thread, ThreadKind, ThreadNode},
};
use blueos_kconfig::CONFIG_NUM_CORES as NUM_CORES;
use core::{
    mem::MaybeUninit,
    ptr,
    sync::atomic::{AtomicUsize, Ordering},
};
use spin::Once;

static mut IDLE_THREAD_BLOCKS: [SystemThreadStorage; NUM_CORES as usize] =
    [const { SystemThreadStorage::new(ThreadKind::Idle) }; NUM_CORES as usize];
pub(super) static mut IDLE_THREADS: [MaybeUninit<ThreadNode>; NUM_CORES as usize] =
    [const { MaybeUninit::zeroed() }; NUM_CORES as usize];

// Idle is per core, disable interrupt to set idle hook
pub type IdleHook = extern "C" fn();
static mut IDLE_HOOK: Option<IdleHook> = None;

pub fn set_idle_hook(hook: IdleHook) {
    unsafe { IDLE_HOOK = Some(hook) };
}

pub(crate) fn get_idle_hook() -> IdleHook {
    if let Some(hook) = unsafe { IDLE_HOOK } {
        hook
    } else {
        arch::idle
    }
}

extern "C" fn fake_idle_thread_entry() {
    unreachable!("Should use real entry specified in start_schedule");
}

fn init_idle_thread(i: usize) {
    let arc = thread::build_static_thread(
        unsafe { &mut IDLE_THREADS[i] },
        unsafe { &mut IDLE_THREAD_BLOCKS[i] },
        MAX_THREAD_PRIORITY,
        thread::RUNNING,
        Entry::C(fake_idle_thread_entry),
        ThreadKind::Idle,
    );
    unsafe {
        RUNNING_THREADS[i].write(arc.clone());
    }
}

pub(super) fn init_idle_threads() {
    for i in 0..NUM_CORES {
        init_idle_thread(i as usize);
    }
}

#[inline]
pub fn current_idle_thread_ref() -> &'static Thread {
    let _dig = support::DisableInterruptGuard::new();
    let id = arch::current_cpu_id();
    unsafe { IDLE_THREADS[id].assume_init_ref() }
}

#[inline]
pub fn current_idle_thread() -> ThreadNode {
    let _dig = support::DisableInterruptGuard::new();
    let id = arch::current_cpu_id();
    unsafe { IDLE_THREADS[id].assume_init_ref() }.clone()
}

#[inline]
pub fn get_idle_thread_ref(cpu_id: usize) -> &'static Thread {
    let _dig = support::DisableInterruptGuard::new();
    unsafe { IDLE_THREADS[cpu_id].assume_init_ref() }
}

#[inline]
pub fn get_idle_thread(cpu_id: usize) -> ThreadNode {
    let _dig = support::DisableInterruptGuard::new();
    unsafe { IDLE_THREADS[cpu_id].assume_init_ref() }.clone()
}
