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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

use crate::sync::{
    barrier::{Barrier, BarrierAttr, WaitResult},
    cond::{Cond, CondAttr},
    mutex::{Mutex, MutexAttr},
    rwlock::{Pshared, Rwlock as RsRwLock, RwlockAttr},
    waitval::Waitval,
};
use alloc::{
    alloc::{alloc as system_alloc, dealloc as system_dealloc},
    collections::btree_map::BTreeMap,
    sync::Arc,
    vec::Vec,
};
use blueos_header::{
    syscalls::NR::{CreateThread, ExitThread, GetSchedParam, GetTid, SchedYield, SetSchedParam},
    thread::{SpawnArgs, DEFAULT_STACK_SIZE, STACK_ALIGN},
};
use blueos_scal::bk_syscall;
use core::{
    alloc::Layout,
    cell::SyncUnsafeCell,
    ffi::{c_int, c_size_t, c_uint, c_void},
    intrinsics::transmute,
    num::{NonZero, NonZeroU32},
    sync::atomic::{AtomicBool, AtomicI32, AtomicI8, AtomicUsize, Ordering},
};
use libc::{
    clockid_t, pthread_attr_t, pthread_barrier_t, pthread_barrierattr_t, pthread_cond_t,
    pthread_condattr_t, pthread_key_t, pthread_mutex_t, pthread_mutexattr_t, pthread_rwlock_t,
    pthread_rwlockattr_t, pthread_spinlock_t, pthread_t, sched_param, timespec, EBUSY, EDEADLK,
    EINVAL, ESRCH,
};
use spin::RwLock;

pub use crate::semaphore::RsSemaphore;
pub use libc::sem_t;

pub const PTHREAD_BARRIER_SERIAL_THREAD: c_int = -1;
pub const PTHREAD_PROCESS_SHARED: c_int = 1;
pub const PTHREAD_PROCESS_PRIVATE: c_int = 0;
pub const SCHED_RR: c_int = 1;
pub const PTHREAD_CANCEL_ASYNCHRONOUS: c_int = 0;
pub const PTHREAD_CANCEL_ENABLE: c_int = 1;
pub const PTHREAD_CANCEL_DEFERRED: c_int = 2;
pub const PTHREAD_CANCEL_DISABLE: c_int = 3;

pub type PosixRoutineEntry = extern "C" fn(arg: *mut c_void) -> *mut c_void;

#[repr(C)]
struct InnerPthreadAttr {
    pub stack_size: usize,
    padding: [usize; 4],
}

// TODO: Current BlueOS kernel doesn't feature using thread-pointer pointing to
// TCB. Use a global map temporarily.
static TCBS: RwLock<BTreeMap<pthread_t, Arc<PthreadTcb>>> = RwLock::new(BTreeMap::new());
static KEYS: RwLock<BTreeMap<pthread_key_t, Dtor>> = RwLock::new(BTreeMap::new());
struct Dtor(Option<extern "C" fn(value: *mut c_void)>);
static KEY_COUNTER: AtomicUsize = AtomicUsize::new(0);

// We are not exposing kernel thread to user level libc, maintain pthread's tcb
// by libc itself.
struct PthreadTcb {
    // Store pthread's Key-Value.
    // FIXME: Rust doesn't allow *mut T in Send trait, use usize here.
    kv: RwLock<BTreeMap<pthread_key_t, usize>>,
    // 0 indicates joinable, 1 indicates detached. -1 indicates the state is
    // frozen and is set in pthread_exit.
    detached: AtomicI8,
    cancel_enabled: AtomicBool,
    retval: SyncUnsafeCell<usize>,
    joint: Barrier,
}

#[inline]
fn get_tcb(tid: pthread_t) -> Option<Arc<PthreadTcb>> {
    TCBS.read().get(&tid).map(Arc::clone)
}

#[inline(always)]
fn get_my_tcb() -> Option<Arc<PthreadTcb>> {
    let tid = pthread_self();
    get_tcb(tid)
}

#[inline]
fn remove_tcb(tid: pthread_t) {
    TCBS.write().remove(&tid);
}

// Prefer using C ABI here since it's stablized.
#[cfg_attr(target_pointer_width = "32", repr(C, align(4)))]
#[cfg_attr(target_pointer_width = "64", repr(C, align(8)))]
struct PosixRoutineInfo {
    pub entry: extern "C" fn(arg: *mut c_void) -> *mut c_void,
    pub arg: *mut c_void,
    pub storage_start: *mut u8,
    pub storage_size: usize,
}

extern "C" fn posix_start_routine(arg: *mut c_void) {
    let routine = unsafe { &*arg.cast::<PosixRoutineInfo>() };
    let retval = (routine.entry)(routine.arg);
    pthread_exit(retval);
}

// This routine will be executed on another stack by kernel.
// The PosixRoutineInfo is stored between [storage_start, storage_start + storage_size),
// that doesn't matter, after the `system_dealloc`, we don't use it anymore.
extern "C" fn posix_cleanup_routine(arg: *mut c_void) {
    assert_ne!(arg, core::ptr::null_mut());
    let routine = unsafe { &*arg.cast::<PosixRoutineInfo>() };
    let layout = Layout::from_size_align(routine.storage_size, STACK_ALIGN).unwrap();
    unsafe { system_dealloc(routine.storage_start, layout) };
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_attr_init(attr: *mut pthread_attr_t) -> c_int {
    let inner_attr = attr as *mut InnerPthreadAttr;
    unsafe {
        (*inner_attr).stack_size = DEFAULT_STACK_SIZE;
    }
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_attr_destroy(_: *mut pthread_attr_t) -> c_int {
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_attr_setstacksize(
    attr: *mut pthread_attr_t,
    stacksize: c_size_t,
) -> c_int {
    unsafe { (*(attr as *mut InnerPthreadAttr)).stack_size = stacksize };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_self() -> pthread_t {
    bk_syscall!(GetTid) as pthread_t
}

/// Same as `pthread_self`
#[no_mangle]
pub extern "C" fn gettid() -> pthread_t {
    bk_syscall!(GetTid) as pthread_t
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_getschedparam(
    thread: pthread_t,
    policy: *mut c_int,
    param: *mut sched_param,
) -> c_int {
    // TODO: Currently kernel only supports SCHED_RR.
    if policy.is_null() || param.is_null() {
        return EINVAL;
    }

    unsafe {
        *policy = SCHED_RR;
        let ret = bk_syscall!(GetSchedParam, thread as usize) as isize;
        if ret < 0 {
            return ret as c_int;
        }
        (*param).sched_priority = ret as c_int;
    }

    0
}

// Only support SCHED_RR, it's the only policy BlueKernel supports.
// this function is a no-op in fact.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_setschedparam(
    thread: pthread_t,
    policy: c_int,
    param: *const sched_param,
) -> c_int {
    if param.is_null() {
        return EINVAL;
    }
    // Only SCHED_RR is supported now. set policy is an non-op.
    // Only set current thread's priority for now.
    let prio = (*param).sched_priority as c_int;
    let ret = bk_syscall!(SetSchedParam, thread as usize, prio) as isize;
    if ret < 0 {
        return ret as c_int;
    }
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_setconcurrency(_concurrency: c_int) -> c_int {
    // BlueKernel supports only 1:1 thread model, so this function is a no-op.
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_setschedprio(_thread: pthread_t, _prio: c_int) -> c_int {
    // BlueKernel currently doesn't support setting thread priority.
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_cancel(thread: pthread_t) -> c_int {
    // now BlueKernel doesn't support full posix cancelation
    // just set cancel_enabled to false, so pthread_testcancel will exit this thread.
    let Some(tcb) = get_tcb(thread) else {
        panic!("{:x}: target tcb is gone!", thread)
    };
    tcb.cancel_enabled.store(true, Ordering::SeqCst);
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_setcancelstate(state: c_int, oldstate: *mut c_int) -> c_int {
    // BlueKernel currently hasn't signal support, no cancel point is implemented.
    // just exit when pthread_testcancel is called.
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("{:x}: My tcb is gone!", tid)
    };
    if !oldstate.is_null() {
        *oldstate = if tcb.cancel_enabled.load(Ordering::SeqCst) {
            PTHREAD_CANCEL_ENABLE
        } else {
            PTHREAD_CANCEL_DISABLE
        }
    }
    match state {
        PTHREAD_CANCEL_ENABLE => tcb.cancel_enabled.store(true, Ordering::SeqCst),
        PTHREAD_CANCEL_DISABLE => tcb.cancel_enabled.store(false, Ordering::SeqCst),
        _ => return EINVAL,
    }
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_setcanceltype(_ty: c_int, _oldty: *mut c_int) -> c_int {
    // BlueKernel currently hasn't signal support, no cancel point is implemented.
    // just exit when pthread_testcancel is called.
    PTHREAD_CANCEL_DEFERRED
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_testcancel() {
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("{:x}: My tcb is gone!", tid)
    };
    if tcb.cancel_enabled.load(Ordering::SeqCst) {
        // We should exit this thread.
        pthread_exit(core::ptr::null_mut());
    }
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_detach(t: pthread_t) -> c_int {
    let Some(tcb) = get_tcb(t) else {
        return ESRCH;
    };
    let old_val = tcb
        .detached
        .compare_exchange(0, 1, Ordering::SeqCst, Ordering::Relaxed);
    let Err(failed_val) = old_val else {
        return 0;
    };
    if failed_val != 1 {
        return EINVAL;
    }
    0
}

// This is used in thread not created by `pthread_create`. Usually at the entry
// of POSIX subsystem.
pub extern "C" fn register_my_tcb() {
    let tid = pthread_self();
    register_posix_tcb(tid as usize, core::ptr::null_mut());
}

extern "C" fn register_posix_tcb(tid: usize, _spawn_args_ptr: *mut SpawnArgs) {
    let tid: pthread_t = unsafe { core::mem::transmute(tid) };
    {
        let tcb = Arc::new(PthreadTcb {
            kv: RwLock::new(BTreeMap::new()),
            cancel_enabled: AtomicBool::new(false),
            detached: AtomicI8::new(0),
            retval: SyncUnsafeCell::new(0),
            joint: Barrier::new(unsafe { NonZero::new(2).unwrap_unchecked() }),
        });
        let mut write = TCBS.write();
        let ret = write.insert(tid, tcb);
        assert!(ret.is_none());
    }
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_create(
    thread: *mut pthread_t,
    attr: *const pthread_attr_t,
    start_routine: PosixRoutineEntry,
    arg: *mut c_void,
) -> c_int {
    let stack_size = if attr.is_null() {
        DEFAULT_STACK_SIZE
    } else {
        unsafe { (*(attr as *const InnerPthreadAttr)).stack_size }
    };
    assert_eq!(stack_size % STACK_ALIGN, 0);
    // We'll put PosixRoutineInfo on the stack.
    let storage_size = stack_size + core::mem::size_of::<PosixRoutineInfo>();
    let layout = Layout::from_size_align(storage_size, STACK_ALIGN).unwrap();
    let storage_start = unsafe { system_alloc(layout) };
    assert_ne!(storage_start, core::ptr::null_mut());
    let posix_routine_info_ptr = unsafe { storage_start.add(stack_size) as *mut c_void };
    assert_eq!(
        posix_routine_info_ptr.align_offset(core::mem::align_of::<PosixRoutineInfo>()),
        0
    );
    let posix_routine_info = unsafe { &mut *(posix_routine_info_ptr as *mut PosixRoutineInfo) };
    posix_routine_info.entry = start_routine;
    posix_routine_info.arg = arg;
    posix_routine_info.storage_start = storage_start;
    posix_routine_info.storage_size = storage_size;
    let mut spawn_args = SpawnArgs {
        spawn_hook: Some(register_posix_tcb),
        entry: posix_start_routine,
        arg: posix_routine_info_ptr,
        cleanup: Some(posix_cleanup_routine),
        stack_start: storage_start,
        stack_size,
    };
    let tid = bk_syscall!(CreateThread, &mut spawn_args as *mut SpawnArgs) as pthread_t;
    if tid == !0 {
        unsafe { system_dealloc(storage_start, layout) };
        return -1;
    }
    unsafe { thread.write_volatile(tid) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_join(tid: pthread_t, retval: *mut *mut c_void) -> c_int {
    if tid == pthread_self() {
        return EDEADLK;
    }
    let Some(tcb) = get_tcb(tid) else {
        return ESRCH;
    };
    let val = tcb.joint.wait();
    if !retval.is_null() {
        unsafe { retval.write(tcb.retval.get().read() as *mut c_void) };
    }
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_exit(retval: *mut c_void) -> ! {
    // pthread_detach must fail if tcb.state != RUNNING.
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("{:x}: My tcb is gone!", tid)
    };
    // We have to cleanup all resources allocated. It *MUST* happen-before `remove_tcb` since
    // dtors might expect the current tcb is still in the TCBS.
    {
        let read_tcb_kv = tcb.kv.read();
        // We have to collect dtors and vals first, since some dtors might write KEYS.
        let mut dtors = Vec::new();
        let mut vals = Vec::new();
        for (key, val) in read_tcb_kv.iter() {
            let keys = KEYS.read();
            if let Some(dtor) = keys.get(key) {
                let ptr: *mut c_void = unsafe { *val as *mut c_void };
                if let Some(f) = dtor.0.as_ref() {
                    dtors.push(*f);
                    vals.push((*key, ptr));
                }
            }
        }
        drop(read_tcb_kv);
        for i in 0..dtors.len() {
            dtors[i](vals[i].1);
        }
    }
    {
        let detached = tcb.detached.swap(-1, Ordering::SeqCst);
        assert_ne!(detached, -1, "pthread_exit should be only called once");
        if detached == 0 {
            unsafe { tcb.retval.get().write(retval as usize) };
            tcb.joint.wait();
        }
    }
    // Must drop in advance since ExitThread never returns.
    drop(tcb);
    // After removing my tcb, other POSIX threads are unable to find me.
    remove_tcb(tid);
    bk_syscall!(ExitThread);
    unreachable!("We have called system call to exit this thread, so should not reach here");
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_setspecific(key: pthread_key_t, val: *const c_void) -> c_int {
    if !KEYS.read().contains_key(&key) {
        return EINVAL;
    }
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("{:x}: My tcb is gone!", tid)
    };
    tcb.kv.write().insert(key, val as usize);
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_getspecific(key: pthread_key_t) -> *mut c_void {
    if !KEYS.read().contains_key(&key) {
        return core::ptr::null_mut();
    }
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("0x{:x}: My tcb is gone!", tid)
    };
    {
        let read_tcb_kv = tcb.kv.read();
        let Some(val) = read_tcb_kv.get(&key) else {
            return core::ptr::null_mut();
        };
        let val = *val;
        drop(read_tcb_kv);
        unsafe { val as *mut c_void }
    }
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_equal(t1: pthread_t, t2: pthread_t) -> c_int {
    (t1 == t2) as c_int
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_getconcurrency() -> c_int {
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_getcpuclockid(_thread: pthread_t, clock_id: *mut clockid_t) -> c_int {
    // todo
    unsafe {
        *clock_id = 0;
    }
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_set_name_np(_t: pthread_t, _name: *const i8) -> c_int {
    // TODO
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_init(condattr: *mut pthread_condattr_t) -> c_int {
    unsafe { condattr.cast::<CondAttr>().write(CondAttr::default()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_destroy(condattr: *mut pthread_condattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(condattr.cast::<CondAttr>()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_getclock(
    condattr: *const pthread_condattr_t,
    clock: *mut clockid_t,
) -> c_int {
    unsafe { *clock = (*condattr.cast::<CondAttr>()).clock };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_getpshared(
    condattr: *const pthread_condattr_t,
    pshared: *mut c_int,
) -> c_int {
    unsafe { *pshared = (*condattr.cast::<CondAttr>()).pshared };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_setpshared(
    condattr: *mut pthread_condattr_t,
    pshared: c_int,
) -> c_int {
    unsafe { (*condattr.cast::<CondAttr>()).pshared = pshared };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_condattr_setclock(
    condattr: *mut pthread_condattr_t,
    clock: clockid_t,
) -> c_int {
    unsafe { (*condattr.cast::<CondAttr>()).clock = clock };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_cond_init(
    cond: *mut pthread_cond_t,
    _attr: *const pthread_condattr_t,
) -> c_int {
    unsafe { cond.cast::<Cond>().write(Cond::new()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_cond_signal(cond: *mut pthread_cond_t) -> c_int {
    unsafe { (*cond.cast::<Cond>()).signal() }.map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_cond_destroy(cond: *mut pthread_cond_t) -> c_int {
    unsafe { core::ptr::drop_in_place(cond.cast::<Cond>()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_cond_wait(
    cond: *mut pthread_cond_t,
    mutex: *mut pthread_mutex_t,
) -> c_int {
    unsafe { (*cond.cast::<Cond>()).wait(&*mutex.cast::<Mutex>()) }.map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_cond_timedwait(
    cond: *mut pthread_cond_t,
    mutex: *mut pthread_mutex_t,
    abstime: *const timespec,
) -> c_int {
    unsafe { (*cond.cast::<Cond>()).timedwait(&*mutex.cast::<Mutex>(), abstime.as_ref().unwrap()) }
        .map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_key_create(
    key: *mut pthread_key_t,
    dtor: Option<extern "C" fn(_: *mut c_void)>,
) -> c_int {
    let new_key = KEY_COUNTER.fetch_add(1, Ordering::Relaxed) as pthread_key_t;
    let mut lock = KEYS.write();
    lock.insert(new_key, Dtor(dtor));
    drop(lock);
    unsafe {
        *key = new_key;
    }
    0
}

// We expect user to have released resources bound to this key in all threads before
// calling this function.
#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_key_delete(key: pthread_key_t) -> c_int {
    KEYS.write().remove(&key);
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutexattr_init(attr: *mut pthread_mutexattr_t) -> c_int {
    unsafe { attr.cast::<MutexAttr>().write(MutexAttr::default()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutexattr_destroy(attr: *mut pthread_mutexattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(attr.cast::<MutexAttr>()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutexattr_settype(attr: *mut pthread_mutexattr_t, ty: c_int) -> c_int {
    unsafe { (*attr.cast::<MutexAttr>()).ty = ty };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutex_init(
    mutex: *mut pthread_mutex_t,
    attr: *const pthread_mutexattr_t,
) -> c_int {
    let attr = unsafe {
        attr.cast::<MutexAttr>()
            .as_ref()
            .copied()
            .unwrap_or_default()
    };
    Mutex::new(&attr).map_or_else(
        |e| e,
        |new| {
            unsafe { mutex.cast::<Mutex>().write(new) };
            0
        },
    )
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutex_lock(mutex: *mut pthread_mutex_t) -> c_int {
    unsafe { (*mutex.cast::<Mutex>()).lock() }.map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutex_unlock(mutex: *mut pthread_mutex_t) -> c_int {
    unsafe { (*mutex.cast::<Mutex>()).unlock() }.map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutex_trylock(mutex: *mut pthread_mutex_t) -> c_int {
    unsafe { (*mutex.cast::<Mutex>()).try_lock() }.map_or_else(|e| e, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_mutex_destroy(mutex: *mut pthread_mutex_t) -> c_int {
    unsafe { core::ptr::drop_in_place(mutex.cast::<Mutex>()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlock_rdlock(rwlock: *mut pthread_rwlock_t) -> c_int {
    unsafe { (*rwlock.cast::<RsRwLock>()).try_acquire_read_lock() }
        .map_or_else(|e| e as c_int, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlock_timedrdlock(
    rwlock: *mut pthread_rwlock_t,
    abstime: *const timespec,
) -> c_int {
    unsafe { (*rwlock.cast::<RsRwLock>()).acquire_read_lock(abstime.as_ref()) }
    //todo return value when timeout
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlock_timedwrlock(
    rwlock: *mut pthread_rwlock_t,
    abstime: *const timespec,
) -> c_int {
    unsafe { (*rwlock.cast::<RsRwLock>()).acquire_write_lock(abstime.as_ref()) }
    //todo return value when timeout
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlock_tryrdlock(rwlock: *mut pthread_rwlock_t) -> c_int {
    unsafe { (*rwlock.cast::<RsRwLock>()).try_acquire_read_lock() }
        .map_or_else(|e| e as c_int, |_| 0)
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlockattr_destroy(attr: *mut pthread_rwlockattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(attr) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_rwlockattr_getpshared(
    attr: *const pthread_rwlockattr_t,
    pshared: *mut c_int,
) -> c_int {
    core::ptr::write(pshared, (*attr.cast::<RwlockAttr>()).pshared.raw());
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_rwlockattr_init(attr: *mut pthread_rwlockattr_t) -> c_int {
    unsafe { attr.cast::<RwlockAttr>().write(RwlockAttr::default()) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_rwlockattr_setpshared(
    attr: *mut pthread_rwlockattr_t,
    pshared: c_int,
) -> c_int {
    (*attr.cast::<RwlockAttr>()).pshared =
        Pshared::from_raw(pshared).expect("invalid pshared in pthread_rwlockattr_setpshared");

    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_init(attr: *mut pthread_barrierattr_t) -> c_int {
    core::ptr::write(attr.cast::<BarrierAttr>(), BarrierAttr::default());
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_destroy(attr: *mut pthread_barrierattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(attr) };
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_destroy(barrier: *mut pthread_barrier_t) -> c_int {
    // Behavior is undefined if any thread is currently waiting when this is called.

    // No-op, currently.
    core::ptr::drop_in_place(barrier.cast::<Barrier>());

    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_init(
    barrier: *mut pthread_barrier_t,
    attr: *const pthread_barrierattr_t,
    count: c_uint,
) -> c_int {
    let _attr = attr
        .cast::<BarrierAttr>()
        .as_ref()
        .copied()
        .unwrap_or_default();

    let Some(count) = NonZeroU32::new(count) else {
        return EINVAL;
    };

    barrier.cast::<Barrier>().write(Barrier::new(count));
    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_wait(barrier: *mut pthread_barrier_t) -> c_int {
    let barrier = &*barrier.cast::<Barrier>();

    match barrier.wait() {
        WaitResult::NotifiedAll => PTHREAD_BARRIER_SERIAL_THREAD,
        WaitResult::Waited => 0,
    }
}

#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_setpshared(
    attr: *mut pthread_barrierattr_t,
    pshared: c_int,
) -> c_int {
    (*attr.cast::<BarrierAttr>()).pshared = pshared;
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_getpshared(
    attr: *const pthread_barrierattr_t,
    pshared: *mut c_int,
) -> c_int {
    core::ptr::write(pshared, (*attr.cast::<BarrierAttr>()).pshared);
    0
}

// FIXME: Move to a separate file
const UNLOCKED: c_int = 0;
const LOCKED: c_int = 1;

#[no_mangle]
pub unsafe extern "C" fn pthread_spin_destroy(spinlock: *mut pthread_spinlock_t) -> c_int {
    let _spinlock = &mut *spinlock.cast::<RsSpinlock>();

    // No-op
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_spin_init(
    spinlock: *mut pthread_spinlock_t,
    _pshared: c_int,
) -> c_int {
    spinlock.cast::<RsSpinlock>().write(RsSpinlock {
        inner: AtomicI32::new(UNLOCKED),
    });

    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_spin_lock(spinlock: *mut pthread_spinlock_t) -> c_int {
    let spinlock = &*spinlock.cast::<RsSpinlock>();

    loop {
        match spinlock.inner.compare_exchange_weak(
            UNLOCKED,
            LOCKED,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(_) => core::hint::spin_loop(),
        }
    }

    0
}
#[no_mangle]
pub unsafe extern "C" fn pthread_spin_trylock(spinlock: *mut pthread_spinlock_t) -> c_int {
    let spinlock = &*spinlock.cast::<RsSpinlock>();

    match spinlock
        .inner
        .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
    {
        Ok(_) => (),
        Err(_) => return EBUSY,
    }

    0
}
#[no_mangle]
pub unsafe extern "C" fn pthread_spin_unlock(spinlock: *mut pthread_spinlock_t) -> c_int {
    let spinlock = &*spinlock.cast::<RsSpinlock>();

    spinlock.inner.store(UNLOCKED, Ordering::Release);

    0
}
pub(crate) struct RsSpinlock {
    pub inner: AtomicI32,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::println;
    use blueos_test_macro::test;
    use core::ptr;

    type WaitPair = (*const Waitval<()>, *const Waitval<()>);

    extern "C" fn block_child_entry(arg: *mut c_void) -> *mut c_void {
        let pair = unsafe { &*(arg as *const WaitPair) };
        let notify = unsafe { &*pair.0 };
        let blocker = unsafe { &*pair.1 };

        notify.post(());
        blocker.wait();
        ptr::null_mut()
    }

    type ReadyPair = (*const Waitval<()>, *const AtomicBool);

    extern "C" fn ready_child_entry(arg: *mut c_void) -> *mut c_void {
        let pair = unsafe { &*(arg as *const ReadyPair) };
        let ready = unsafe { &*pair.0 };
        let release = unsafe { &*pair.1 };
        ready.post(());
        loop {
            if release.load(Ordering::Acquire) {
                break;
            }
            bk_syscall!(SchedYield);
        }
        ptr::null_mut()
    }

    macro_rules! check_align {
        ($lhs:ident, $rhs:ident) => {
            assert_eq!(align_of::<$lhs>(), align_of::<$rhs>())
        };
    }

    macro_rules! check_size {
        ($lhs:ident, $rhs:ident) => {
            assert_eq!(size_of::<$lhs>(), size_of::<$rhs>())
        };
    }

    #[test]
    fn check_type_consistency() {
        check_align!(pthread_mutex_t, Mutex);
        check_size!(pthread_mutex_t, Mutex);
        check_align!(pthread_mutexattr_t, MutexAttr);
        check_size!(pthread_mutexattr_t, MutexAttr);
        check_align!(pthread_cond_t, Cond);
        check_size!(pthread_cond_t, Cond);
        check_align!(usize, pthread_t);
        check_size!(usize, pthread_t);
        check_align!(pthread_attr_t, InnerPthreadAttr);
        check_size!(pthread_attr_t, InnerPthreadAttr);
        check_align!(pthread_condattr_t, CondAttr);
        check_size!(pthread_condattr_t, CondAttr);
        check_align!(pthread_rwlockattr_t, RwlockAttr);
        check_size!(pthread_rwlockattr_t, RwlockAttr);
        check_align!(pthread_rwlock_t, RsRwLock);
        check_size!(pthread_rwlock_t, RsRwLock);
        check_align!(pthread_barrierattr_t, BarrierAttr);
        check_size!(pthread_barrierattr_t, BarrierAttr);
        check_align!(pthread_barrier_t, Barrier);
        check_size!(pthread_barrier_t, Barrier);
        check_align!(sem_t, RsSemaphore);
        check_size!(sem_t, RsSemaphore);
        check_align!(pthread_spinlock_t, RsSpinlock);
        check_size!(pthread_spinlock_t, RsSpinlock);
    }

    #[test]
    fn stress_sched_yield() {
        {
            let n = 16;
            for _i in 0..n {
                #[cfg(target_arch = "riscv64")]
                bk_syscall!(SchedYield);
            }
        }
    }

    #[test]
    #[cfg(target_arch = "arm")] // FIXME: riscv64 test hangs here
    fn check_pthread_setschedparam_ready_thread() {
        let ready = Waitval::new();
        let release = AtomicBool::new(false);
        let mut pair: ReadyPair = (&ready as *const _, &release as *const _);

        let mut th: pthread_t = 0;
        let ret = unsafe {
            pthread_create(
                &mut th,
                ptr::null(),
                ready_child_entry,
                (&mut pair as *mut ReadyPair as *mut c_void),
            )
        };
        assert_eq!(ret, 0);

        ready.wait();

        let desired = sched_param { sched_priority: 3 };
        let ret = unsafe { pthread_setschedparam(th, SCHED_RR, &desired) };

        let mut policy = 0;
        let mut observed = sched_param { sched_priority: 0 };
        pthread_getschedparam(th, &mut policy, &mut observed);

        assert_eq!(policy, SCHED_RR);
        assert_eq!(observed.sched_priority, desired.sched_priority);

        release.store(true, Ordering::Release);

        unsafe {
            pthread_join(th, ptr::null_mut());
        }
    }

    #[test]
    fn check_pthread_setschedparam_running_thread() {
        let tid = pthread_self();
        let mut policy = 0;
        let mut current = sched_param { sched_priority: 0 };
        assert_eq!(pthread_getschedparam(tid, &mut policy, &mut current), 0);

        assert_eq!(unsafe { pthread_setschedparam(tid, policy, &current) }, 0);
    }

    #[test]
    #[cfg(target_arch = "arm")] // FIXME: riscv64 test hangs here
    fn check_pthread_setschedparam_blocked_thread() {
        let notify = Waitval::new();
        let blocker = Waitval::new();
        let mut pair: WaitPair = (&notify as *const _, &blocker as *const _);

        let mut th: pthread_t = 0;
        let ret = unsafe {
            pthread_create(
                &mut th,
                ptr::null(),
                block_child_entry,
                (&mut pair as *mut WaitPair as *mut c_void),
            )
        };
        assert_eq!(ret, 0);

        notify.wait();

        let desired = sched_param { sched_priority: 2 };
        unsafe { pthread_setschedparam(th, SCHED_RR, &desired) };

        let mut policy = 0;
        let mut observed = sched_param { sched_priority: 0 };
        pthread_getschedparam(th, &mut policy, &mut observed);
        assert_eq!(policy, SCHED_RR);
        assert_eq!(observed.sched_priority, desired.sched_priority);

        blocker.post(());
        unsafe {
            pthread_join(th, ptr::null_mut());
        }
    }
}
