// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

// POSIX syncs/TCB implementations for the newlib_mps3_an547 target.
// All types ABI consistency with newlib.

use alloc::{
    alloc::{alloc as system_alloc, dealloc as system_dealloc},
    boxed::Box,
    collections::btree_map::BTreeMap,
    sync::Arc,
    vec::Vec,
};
use blueos_header::{
    syscalls::NR::{AtomicWait, AtomicWake, CreateThread, ExitThread, GetTid},
    thread::{SpawnArgs, DEFAULT_STACK_SIZE, STACK_ALIGN},
};
use blueos_scal::bk_syscall;
use core::{
    alloc::Layout,
    cell::{SyncUnsafeCell, UnsafeCell},
    ffi::{c_int, c_uint, c_void},
    num::NonZeroU32,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicBool, AtomicI8, AtomicUsize, Ordering},
};
use libc::{
    clockid_t, pthread_attr_t, pthread_barrier_t, pthread_barrierattr_t, pthread_key_t,
    pthread_rwlockattr_t, pthread_t, timespec, EAGAIN, EBUSY, EDEADLK, EINVAL, EPERM, ESRCH,
    ETIMEDOUT, PTHREAD_MUTEX_DEFAULT, PTHREAD_MUTEX_ERRORCHECK, PTHREAD_MUTEX_NORMAL,
    PTHREAD_MUTEX_RECURSIVE, PTHREAD_PROCESS_PRIVATE,
};
use spin::RwLock;

use crate::{__sFILE, _reent};

pub const PTHREAD_BARRIER_SERIAL_THREAD: c_int = -1;
pub const PTHREAD_PROCESS_SHARED: c_int = 1;
pub const PTHREAD_PROCESS_PRIVATE_CONST: c_int = 0;

pub type PosixRoutineEntry = extern "C" fn(arg: *mut c_void) -> *mut c_void;

// --- futex helpers ---
const FUTEX_WAIT_RESULT_WAITED: c_int = 0;
const FUTEX_WAIT_RESULT_STALE: c_int = 1;
const FUTEX_WAIT_RESULT_TIMED_OUT: c_int = 2;

fn futex_wake(atomic: &AtomicUsize, val: usize) -> c_int {
    let mut woken: usize = val;
    bk_syscall!(
        AtomicWake,
        atomic.as_ptr() as usize,
        &mut woken as *mut usize
    );
    woken as c_int
}

fn futex_wait(atomic: &AtomicUsize, val: usize, timeout: Option<&timespec>) -> c_int {
    bk_syscall!(
        AtomicWait,
        atomic.as_ptr() as usize,
        val,
        timeout.map_or(core::ptr::null(), |t| t as *const timespec)
    ) as c_int
}

// --- GenericMutex ---
const UNLOCKED: usize = 0;
const LOCKED: usize = 1;
const WAITING: usize = 2;

pub(crate) struct GenericMutex<T> {
    lock: AtomicLock,
    content: UnsafeCell<T>,
}

unsafe impl<T: Send + Sync> Send for GenericMutex<T> {}
unsafe impl<T: Send + Sync> Sync for GenericMutex<T> {}

impl<T> GenericMutex<T> {
    pub(crate) const fn new(content: T) -> Self {
        Self {
            lock: AtomicLock::new(UNLOCKED),
            content: UnsafeCell::new(content),
        }
    }

    pub(crate) unsafe fn manual_lock(&self) -> &mut T {
        unsafe { manual_lock_generic(&self.lock) };
        unsafe { &mut *self.content.get() }
    }

    pub(crate) unsafe fn manual_unlock(&self) {
        unsafe { manual_unlock_generic(&self.lock) }
    }

    pub(crate) unsafe fn manual_try_lock(&self) -> Result<&mut T, c_int> {
        if unsafe { manual_try_lock_generic(&self.lock) } {
            Ok(unsafe { &mut *self.content.get() })
        } else {
            Err(0)
        }
    }

    pub(crate) fn lock(&self) -> MutexGuard<'_, T> {
        MutexGuard {
            mutex: self,
            content: unsafe { self.manual_lock() },
        }
    }
}

pub(crate) struct MutexGuard<'a, T: 'a> {
    pub(crate) mutex: &'a GenericMutex<T>,
    content: &'a mut T,
}

impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.content
    }
}

impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.content
    }
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        unsafe { self.mutex.manual_unlock() };
    }
}

struct AtomicLock {
    atomic: AtomicUsize,
}

impl Deref for AtomicLock {
    type Target = AtomicUsize;
    fn deref(&self) -> &Self::Target {
        &self.atomic
    }
}

impl AtomicLock {
    const fn new(value: usize) -> Self {
        Self {
            atomic: AtomicUsize::new(value),
        }
    }
}

unsafe fn manual_try_lock_generic(word: &AtomicUsize) -> bool {
    word.compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
        .is_ok()
}

unsafe fn manual_lock_generic(word: &AtomicUsize) {
    wait_until_generic(
        word,
        |lock| {
            lock.compare_exchange_weak(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
                .map(|_| AttemptStatus::Desired)
                .unwrap_or_else(|e| match e {
                    WAITING => AttemptStatus::Waiting,
                    _ => AttemptStatus::Other,
                })
        },
        |lock| match lock
            .compare_exchange_weak(LOCKED, WAITING, Ordering::SeqCst, Ordering::SeqCst)
            .unwrap_or_else(|e| e)
        {
            UNLOCKED => AttemptStatus::Desired,
            WAITING => AttemptStatus::Waiting,
            _ => AttemptStatus::Other,
        },
        WAITING,
    );
}

unsafe fn manual_unlock_generic(word: &AtomicUsize) {
    if word.swap(UNLOCKED, Ordering::Release) == WAITING {
        futex_wake(word, usize::MAX);
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AttemptStatus {
    Desired,
    Waiting,
    Other,
}

fn wait_until_generic<F1, F2>(word: &AtomicUsize, attempt: F1, mark_long: F2, long: usize)
where
    F1: Fn(&AtomicUsize) -> AttemptStatus,
    F2: Fn(&AtomicUsize) -> AttemptStatus,
{
    for _ in 0..999 {
        core::hint::spin_loop();
        if attempt(word) == AttemptStatus::Desired {
            return;
        }
    }
    let mut previous = attempt(word);
    loop {
        if previous == AttemptStatus::Desired {
            return;
        }
        if previous == AttemptStatus::Waiting || mark_long(word) != AttemptStatus::Desired {
            futex_wait(word, long, None);
        }
        previous = attempt(word);
    }
}

// ---  MutexAttr (20 bytes, matching __SIZEOF_PTHREAD_MUTEXATTR_T) ---
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct MutexAttr {
    pub is_initialized: c_int,
    pub process_shared: c_int,
    pub ty: c_int,
    pub recursive: c_int,
    _padding: c_int,
}

impl Default for MutexAttr {
    fn default() -> Self {
        Self {
            is_initialized: 1,
            process_shared: PTHREAD_PROCESS_PRIVATE,
            ty: PTHREAD_MUTEX_DEFAULT,
            recursive: 0,
            _padding: 0,
        }
    }
}

// ---  Mutex ---
#[repr(u8)]
#[derive(PartialEq, Debug)]
enum Ty {
    Normal,
    Def,
    Errck,
    Recursive,
}

pub struct Mutex {
    inner: AtomicUsize,
    recursive_count: AtomicUsize,
    ty: Ty,
}

const STATE_UNLOCKED: usize = 0;
const WAITING_BIT: usize = 1 << 31;
const INDEX_MASK: usize = !WAITING_BIT;
const RECURSIVE_COUNT_MAX_INCLUSIVE: usize = usize::MAX;

impl Mutex {
    fn new_with_attr(attr: &MutexAttr) -> Result<Self, c_int> {
        Ok(Self {
            inner: AtomicUsize::new(STATE_UNLOCKED),
            recursive_count: AtomicUsize::new(0),
            ty: match attr.ty {
                PTHREAD_MUTEX_DEFAULT => Ty::Def,
                PTHREAD_MUTEX_ERRORCHECK => Ty::Errck,
                PTHREAD_MUTEX_RECURSIVE => Ty::Recursive,
                PTHREAD_MUTEX_NORMAL => Ty::Normal,
                _ => return Err(EINVAL),
            },
        })
    }

    pub(crate) const fn new_recursive() -> Self {
        Self {
            inner: AtomicUsize::new(STATE_UNLOCKED),
            recursive_count: AtomicUsize::new(0),
            ty: Ty::Recursive,
        }
    }

    pub(crate) const fn new() -> Self {
        Self {
            inner: AtomicUsize::new(STATE_UNLOCKED),
            recursive_count: AtomicUsize::new(0),
            ty: Ty::Def,
        }
    }

    fn lock_inner(&self, deadline: Option<&timespec>) -> Result<(), c_int> {
        let this_thread = pthread_self();
        loop {
            let result = self.inner.compare_exchange_weak(
                STATE_UNLOCKED,
                this_thread.try_into().unwrap(),
                Ordering::Acquire,
                Ordering::Relaxed,
            );
            match result {
                Ok(_) => {
                    if self.ty == Ty::Recursive {
                        self.increment_recursive_count()?;
                    }
                    return Ok(());
                }
                Err(thread)
                    if thread & INDEX_MASK == this_thread.try_into().unwrap()
                        && self.ty == Ty::Recursive =>
                {
                    self.increment_recursive_count()?;
                    return Ok(());
                }
                Err(thread)
                    if thread & INDEX_MASK == this_thread.try_into().unwrap()
                        && self.ty == Ty::Errck =>
                {
                    return Err(EAGAIN);
                }
                Err(thread) if thread & INDEX_MASK == 0 => {
                    continue;
                }
                Err(_) => {
                    if futex_wait(&self.inner, result.unwrap_err(), deadline)
                        == FUTEX_WAIT_RESULT_TIMED_OUT
                    {
                        return Err(ETIMEDOUT);
                    }
                }
            }
        }
    }

    pub(crate) fn lock(&self) -> Result<(), c_int> {
        self.lock_inner(None)
    }

    fn lock_with_timeout(&self, deadline: &timespec) -> Result<(), c_int> {
        self.lock_inner(Some(deadline))
    }

    fn increment_recursive_count(&self) -> Result<(), c_int> {
        let prev = self.recursive_count.load(Ordering::Relaxed);
        if prev == RECURSIVE_COUNT_MAX_INCLUSIVE {
            return Err(EAGAIN);
        }
        self.recursive_count.store(prev + 1, Ordering::Relaxed);
        Ok(())
    }

    pub(crate) fn try_lock(&self) -> Result<(), c_int> {
        let this_thread = pthread_self();
        let result = self.inner.compare_exchange(
            STATE_UNLOCKED,
            this_thread.try_into().unwrap(),
            Ordering::Acquire,
            Ordering::Relaxed,
        );
        if self.ty == Ty::Recursive {
            match result {
                Err(index) if index & INDEX_MASK != this_thread.try_into().unwrap() => {
                    return Err(EBUSY)
                }
                _ => (),
            }
            self.increment_recursive_count()?;
            return Ok(());
        }
        match result {
            Ok(_) => Ok(()),
            Err(index)
                if index & INDEX_MASK == this_thread.try_into().unwrap()
                    && self.ty == Ty::Errck =>
            {
                Err(EDEADLK)
            }
            Err(_) => Err(EBUSY),
        }
    }

    pub(crate) fn unlock(&self) -> Result<(), c_int> {
        if matches!(self.ty, Ty::Recursive | Ty::Errck) {
            if self.inner.load(Ordering::Relaxed) & INDEX_MASK != pthread_self().try_into().unwrap()
            {
                return Err(EPERM);
            }
            core::sync::atomic::fence(Ordering::Acquire);
        }
        if self.ty == Ty::Recursive {
            let next = self.recursive_count.load(Ordering::Relaxed) - 1;
            self.recursive_count.store(next, Ordering::Relaxed);
            if next > 0 {
                return Ok(());
            }
        }
        self.inner.store(STATE_UNLOCKED, Ordering::Release);
        futex_wake(&self.inner, usize::MAX);
        Ok(())
    }
}

/// Standalone const fn for creating a recursive mutex, used by retarget.rs.
pub(crate) const fn new_recursive_mutex() -> Mutex {
    Mutex::new_recursive()
}

// ---  CondAttr and Cond ---
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct CondAttr {
    pub clock: clockid_t,
    pub pshared: c_int,
}

#[repr(align(8))]
pub struct Cond {
    cur: AtomicUsize,
    prev: AtomicUsize,
}

impl Cond {
    pub(crate) fn new() -> Self {
        Self {
            cur: AtomicUsize::new(0),
            prev: AtomicUsize::new(0),
        }
    }

    fn wake(&self, count: usize) -> Result<(), c_int> {
        let p = self.prev.load(Ordering::Relaxed);
        self.cur.store(p.wrapping_add(1), Ordering::Relaxed);
        futex_wake(&self.cur, count);
        Ok(())
    }

    pub(crate) fn broadcast(&self) -> Result<(), c_int> {
        self.wake(usize::MAX)
    }

    pub(crate) fn signal(&self) -> Result<(), c_int> {
        self.broadcast()
    }

    pub(crate) fn timedwait(&self, mutex: &Mutex, timeout: &timespec) -> Result<(), c_int> {
        self.wait_inner(mutex, Some(timeout))
    }

    fn wait_inner(&self, mutex: &Mutex, timeout: Option<&timespec>) -> Result<(), c_int> {
        self.wait_inner_generic(
            || mutex.unlock(),
            || mutex.lock(),
            |deadline| mutex.lock_with_timeout(deadline),
            timeout,
        )
    }

    fn wait_inner_generic(
        &self,
        unlock: impl FnOnce() -> Result<(), c_int>,
        lock: impl FnOnce() -> Result<(), c_int>,
        lock_with_timeout: impl FnOnce(&timespec) -> Result<(), c_int>,
        deadline: Option<&timespec>,
    ) -> Result<(), c_int> {
        let current = self.cur.load(Ordering::Relaxed);
        self.prev.store(current, Ordering::Relaxed);
        let _ = unlock();
        match deadline {
            Some(deadline) => {
                futex_wait(&self.cur, current, Some(deadline));
                let _ = lock_with_timeout(deadline);
            }
            None => {
                futex_wait(&self.cur, current, None);
                let _ = lock();
            }
        }
        Ok(())
    }

    pub(crate) fn wait(&self, mutex: &Mutex) -> Result<(), c_int> {
        self.wait_inner(mutex, None)
    }

    pub(crate) fn wait_inner_typedmutex<'lock, T>(
        &self,
        guard: MutexGuard<'lock, T>,
    ) -> MutexGuard<'lock, T> {
        let mut newguard = None;
        let lock = guard.mutex;
        self.wait_inner_generic(
            move || {
                drop(guard);
                Ok(())
            },
            || {
                newguard = Some(lock.lock());
                Ok(())
            },
            |_| unreachable!(),
            None,
        )
        .unwrap();
        newguard.unwrap()
    }
}

// ---  BarrierAttr and Barrier  ---
#[derive(Clone, Copy)]
pub struct BarrierAttr {
    pub pshared: c_int,
}

impl Default for BarrierAttr {
    fn default() -> Self {
        Self {
            pshared: PTHREAD_PROCESS_PRIVATE,
        }
    }
}

struct BarrierInner {
    count: u32,
    gen_id: u32,
}

pub struct Barrier {
    original_count: NonZeroU32,
    lock: GenericMutex<BarrierInner>,
    cvar: Cond,
}

pub enum WaitResult {
    Waited,
    NotifiedAll,
}

impl Barrier {
    pub(crate) fn new(count: NonZeroU32) -> Self {
        Self {
            original_count: count,
            lock: GenericMutex::new(BarrierInner {
                count: 0,
                gen_id: 0,
            }),
            cvar: Cond::new(),
        }
    }

    pub(crate) fn wait(&self) -> WaitResult {
        let mut guard = self.lock.lock();
        let gen_id = guard.gen_id;
        guard.count += 1;
        if guard.count == self.original_count.get() {
            guard.gen_id = guard.gen_id.wrapping_add(1);
            guard.count = 0;
            let _ = self.cvar.broadcast();
            drop(guard);
            WaitResult::NotifiedAll
        } else {
            while guard.gen_id == gen_id {
                guard = self.cvar.wait_inner_typedmutex(guard);
            }
            WaitResult::Waited
        }
    }
}

// ---  RwlockAttr  ---
#[derive(Clone, Copy, Default)]
pub struct RwlockAttr {
    pub pshared: u8,
}

// --- Pthread types ---
#[repr(C)]
struct InnerPthreadAttr {
    pub stack_size: usize,
    padding: [usize; 4],
}

static TCBS: RwLock<BTreeMap<pthread_t, Arc<PthreadTcb>>> = RwLock::new(BTreeMap::new());
static KEYS: RwLock<BTreeMap<pthread_key_t, Dtor>> = RwLock::new(BTreeMap::new());
struct Dtor(Option<extern "C" fn(value: *mut c_void)>);
static KEY_COUNTER: AtomicUsize = AtomicUsize::new(0);

struct PthreadTcb {
    kv: RwLock<BTreeMap<pthread_key_t, usize>>,
    detached: AtomicI8,
    cancel_enabled: AtomicBool,
    retval: SyncUnsafeCell<usize>,
    joint: Barrier,
    reent: SyncUnsafeCell<_reent>,
}

unsafe impl Send for PthreadTcb {}
unsafe impl Sync for PthreadTcb {}

impl Drop for PthreadTcb {
    fn drop(&mut self) {
        unsafe { _reclaim_reent(self.reent.get()) };
    }
}

#[inline]
fn get_tcb(tid: pthread_t) -> Option<Arc<PthreadTcb>> {
    TCBS.read().get(&tid).map(Arc::clone)
}

#[inline]
fn remove_tcb(tid: pthread_t) {
    TCBS.write().remove(&tid);
}

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

extern "C" fn posix_cleanup_routine(arg: *mut c_void) {
    assert_ne!(arg, core::ptr::null_mut());
    let routine = unsafe { &*arg.cast::<PosixRoutineInfo>() };
    let layout = Layout::from_size_align(routine.storage_size, STACK_ALIGN).unwrap();
    unsafe { system_dealloc(routine.storage_start, layout) };
}

// --- __getreent and externs for newlib ---
#[no_mangle]
pub unsafe extern "C" fn __getreent() -> *mut _reent {
    let tid = pthread_self();
    let tcb = get_tcb(tid);
    match tcb {
        Some(tcb) => tcb.reent.get(),
        None => unsafe { _impure_ptr },
    }
}

extern "C" {
    static _impure_ptr: *mut _reent;
    fn _reclaim_reent(ptr: *mut _reent);
    static mut __sf: [__sFILE; 3];
    fn __sinit(ptr: *mut _reent);
}

/// cbindgen:ignore
#[no_mangle]
pub extern "C" fn register_my_posix_tcb() {
    let tid = pthread_self();
    register_posix_tcb(tid as usize, core::ptr::null_mut());
}

extern "C" fn register_posix_tcb(tid: usize, _spawn_args_ptr: *mut SpawnArgs) {
    let tid: pthread_t = unsafe { core::mem::transmute(tid) };
    let tcb = Arc::new(PthreadTcb {
        kv: RwLock::new(BTreeMap::new()),
        cancel_enabled: AtomicBool::new(false),
        detached: AtomicI8::new(0),
        retval: SyncUnsafeCell::new(0),
        joint: Barrier::new(unsafe { core::num::NonZero::new(2).unwrap_unchecked() }),
        reent: SyncUnsafeCell::new(unsafe { core::mem::zeroed::<_reent>() }),
    });
    let reent = unsafe { &mut *tcb.reent.get() };
    unsafe {
        reent._stdin = &mut __sf[0];
        reent._stdout = &mut __sf[1];
        reent._stderr = &mut __sf[2];
        reent._new._reent._rand_next = 1;
        reent._new._reent._r48._seed = [0x330e, 0xabcd, 0x1234];
        reent._new._reent._r48._mult = [0xe66d, 0xdeec, 0x0005];
        reent._new._reent._r48._add = 0x000b;
        __sinit(reent as *mut _reent);
    }

    let mut write = TCBS.write();
    let ret = write.insert(tid, tcb);
    assert!(ret.is_none());
}

// --- pthread core functions ---
#[no_mangle]
pub extern "C" fn pthread_self() -> pthread_t {
    bk_syscall!(GetTid) as pthread_t
}

#[no_mangle]
pub extern "C" fn pthread_attr_init(attr: *mut pthread_attr_t) -> c_int {
    let inner_attr = attr as *mut InnerPthreadAttr;
    unsafe {
        (*inner_attr).stack_size = DEFAULT_STACK_SIZE;
    }
    0
}

pub extern "C" fn pthread_attr_destroy(_: *mut pthread_attr_t) -> c_int {
    0
}

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn pthread_setconcurrency(_concurrency: c_int) -> c_int {
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cancel(thread: pthread_t) -> c_int {
    let Some(tcb) = get_tcb(thread) else {
        panic!("{:x}: target tcb is gone!", thread)
    };
    tcb.cancel_enabled.store(true, Ordering::SeqCst);
    0
}

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

#[no_mangle]
pub extern "C" fn pthread_join(tid: pthread_t, retval: *mut *mut c_void) -> c_int {
    if tid == pthread_self() {
        return EDEADLK;
    }
    let Some(tcb) = get_tcb(tid) else {
        return ESRCH;
    };
    let _val = tcb.joint.wait();
    if !retval.is_null() {
        unsafe { retval.write(tcb.retval.get().read() as *mut c_void) };
    }
    0
}

#[no_mangle]
pub extern "C" fn pthread_exit(retval: *mut c_void) -> ! {
    let tid = pthread_self();
    let Some(tcb) = get_tcb(tid) else {
        panic!("{:x}: My tcb is gone!", tid)
    };
    {
        let read_tcb_kv = tcb.kv.read();
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
    drop(tcb);
    remove_tcb(tid);
    bk_syscall!(ExitThread);
    unreachable!("We have called system call to exit this thread, so should not reach here");
}

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

#[no_mangle]
pub extern "C" fn pthread_key_delete(key: pthread_key_t) -> c_int {
    KEYS.write().remove(&key);
    0
}

// --- pthread_once ---
#[no_mangle]
pub extern "C" fn pthread_once(once: *mut i32, init: extern "C" fn()) -> c_int {
    if once.is_null() {
        return EINVAL;
    }
    unsafe {
        let init_executed_ptr = once.add(1);
        if core::ptr::read_volatile(init_executed_ptr) == 0 {
            core::ptr::write_volatile(init_executed_ptr, 2);
            init();
        }
    }
    0
}

// --- cond functions  ---
#[no_mangle]
pub extern "C" fn pthread_condattr_init(condattr: *mut CondAttr) -> c_int {
    unsafe { condattr.write(CondAttr::default()) };
    0
}

#[no_mangle]
pub extern "C" fn pthread_condattr_destroy(condattr: *mut CondAttr) -> c_int {
    unsafe { core::ptr::drop_in_place(condattr) };
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_init(
    cond_ptr: *mut *mut Cond,
    _attr: *const CondAttr,
) -> c_int {
    if cond_ptr.is_null() {
        return EINVAL;
    }
    let boxed = Box::new(Cond::new());
    let raw = Box::into_raw(boxed);
    cond_ptr.write(raw);
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_wait(
    cond_ptr: *mut *mut Cond,
    mutex_ptr: *mut *mut Mutex,
) -> c_int {
    if cond_ptr.is_null() || mutex_ptr.is_null() {
        return EINVAL;
    }

    let current_cond_val = *cond_ptr;
    if current_cond_val as usize == 0xFFFFFFFF || current_cond_val.is_null() {
        let boxed_cond = Box::new(Cond::new());
        let raw_cond_ptr = Box::into_raw(boxed_cond);
        *cond_ptr = raw_cond_ptr;
    }

    let real_cond = &**cond_ptr;
    let real_mutex = &**mutex_ptr;

    match real_cond.wait(real_mutex) {
        Ok(_) => 0,
        Err(_) => EINVAL,
    }
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_signal(cond_ptr: *mut *mut Cond) -> c_int {
    if cond_ptr.is_null() {
        return EINVAL;
    }

    let current_val = *cond_ptr;
    if current_val.is_null() || current_val as usize == 0xFFFFFFFF {
        return 0;
    }

    let real_cond = &*current_val;
    let _ = real_cond.signal();
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_broadcast(cond_ptr: *mut *mut Cond) -> c_int {
    if cond_ptr.is_null() {
        return EINVAL;
    }

    let current_val = *cond_ptr;
    if current_val.is_null() || current_val as usize == 0xFFFFFFFF {
        return 0;
    }

    let real_cond = &*current_val;
    let _ = real_cond.broadcast();
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_destroy(cond_ptr: *mut *mut Cond) -> c_int {
    if cond_ptr.is_null() {
        return EINVAL;
    }

    let current_val = *cond_ptr;
    if !current_val.is_null() && current_val as usize != 0xFFFFFFFF {
        let _boxed_cond = Box::from_raw(current_val);
        *cond_ptr = core::ptr::null_mut();
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_cond_timedwait(
    cond_ptr: *mut *mut Cond,
    mutex_ptr: *mut *mut Mutex,
    abstime: *const timespec,
) -> c_int {
    if cond_ptr.is_null() || mutex_ptr.is_null() {
        return EINVAL;
    }

    let current_cond_val = *cond_ptr;
    if current_cond_val as usize == 0xFFFFFFFF || current_cond_val.is_null() {
        let boxed_cond = Box::new(Cond::new());
        let raw_cond_ptr = Box::into_raw(boxed_cond);
        *cond_ptr = raw_cond_ptr;
    }

    let real_cond = &**cond_ptr;
    let real_mutex = &**mutex_ptr;

    match real_cond.timedwait(real_mutex, abstime.as_ref().unwrap()) {
        Ok(_) => 0,
        Err(_) => EINVAL,
    }
}

// --- mutex functions  ---
#[no_mangle]
pub extern "C" fn pthread_mutexattr_init(attr: *mut MutexAttr) -> c_int {
    unsafe { attr.write(MutexAttr::default()) };
    0
}

#[no_mangle]
pub extern "C" fn pthread_mutexattr_destroy(attr: *mut MutexAttr) -> c_int {
    unsafe { core::ptr::drop_in_place(attr) };
    0
}

#[no_mangle]
pub extern "C" fn pthread_mutexattr_settype(attr: *mut MutexAttr, ty: c_int) -> c_int {
    unsafe { (*attr).ty = ty };
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_mutex_init(
    mutex_ptr: *mut *mut Mutex,
    attr: *const MutexAttr,
) -> c_int {
    if mutex_ptr.is_null() {
        return EINVAL;
    }

    let local_attr = attr.as_ref().copied().unwrap_or_default();

    match Mutex::new_with_attr(&local_attr) {
        Ok(new_mutex) => {
            let boxed = Box::new(new_mutex);
            let raw_ptr = Box::into_raw(boxed);
            mutex_ptr.write(raw_ptr);
            0
        }
        Err(e) => e,
    }
}

unsafe fn get_or_init_mutex<'a>(mutex_ptr: *mut *mut Mutex) -> &'a Mutex {
    let current_val = *mutex_ptr;

    if current_val as usize == 0xFFFFFFFF || current_val.is_null() {
        let new_mutex = Mutex::new();
        let boxed = Box::new(new_mutex);
        let raw_ptr = Box::into_raw(boxed);
        mutex_ptr.write(raw_ptr);
        return &*raw_ptr;
    }

    &*current_val
}

#[no_mangle]
pub unsafe extern "C" fn pthread_mutex_lock(mutex_ptr: *mut *mut Mutex) -> c_int {
    if mutex_ptr.is_null() {
        return EINVAL;
    }
    let real_mutex = get_or_init_mutex(mutex_ptr);
    real_mutex.lock().map_or_else(|e| e, |_| 0)
}

#[no_mangle]
pub unsafe extern "C" fn pthread_mutex_unlock(mutex_ptr: *mut *mut Mutex) -> c_int {
    if mutex_ptr.is_null() {
        return EINVAL;
    }
    let real_mutex = get_or_init_mutex(mutex_ptr);
    real_mutex.unlock().map_or_else(|e| e, |_| 0)
}

#[no_mangle]
pub unsafe extern "C" fn pthread_mutex_trylock(mutex_ptr: *mut *mut Mutex) -> c_int {
    if mutex_ptr.is_null() {
        return EINVAL;
    }
    let real_mutex = get_or_init_mutex(mutex_ptr);
    real_mutex.try_lock().map_or_else(|e| e, |_| 0)
}

#[no_mangle]
pub unsafe extern "C" fn pthread_mutex_destroy(mutex_ptr: *mut *mut Mutex) -> c_int {
    if mutex_ptr.is_null() {
        return EINVAL;
    }

    let current_val = *mutex_ptr;
    if !current_val.is_null() && current_val as usize != 0xFFFFFFFF {
        let _boxed = Box::from_raw(current_val);
        mutex_ptr.write(core::ptr::null_mut());
    }
    0
}

// --- barrier functions ---
#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_init(attr: *mut pthread_barrierattr_t) -> c_int {
    core::ptr::write(attr.cast::<BarrierAttr>(), BarrierAttr::default());
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_barrierattr_destroy(attr: *mut pthread_barrierattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(attr.cast::<BarrierAttr>()) };
    0
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

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_destroy(barrier: *mut Barrier) -> c_int {
    core::ptr::drop_in_place(barrier);
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_init(
    barrier: *mut Barrier,
    attr: *const BarrierAttr,
    count: c_uint,
) -> c_int {
    let _attr = attr.as_ref().copied().unwrap_or_default();

    let Some(count) = NonZeroU32::new(count) else {
        return EINVAL;
    };

    barrier.write(Barrier::new(count));
    0
}

#[no_mangle]
pub unsafe extern "C" fn pthread_barrier_wait(barrier: *mut Barrier) -> c_int {
    let barrier = &*barrier;
    match barrier.wait() {
        WaitResult::NotifiedAll => PTHREAD_BARRIER_SERIAL_THREAD,
        WaitResult::Waited => 0,
    }
}

// --- rwlock attr functions ---
#[no_mangle]
pub extern "C" fn pthread_rwlockattr_init(attr: *mut pthread_rwlockattr_t) -> c_int {
    unsafe { attr.cast::<RwlockAttr>().write(RwlockAttr::default()) };
    0
}

#[no_mangle]
pub extern "C" fn pthread_rwlockattr_destroy(attr: *mut pthread_rwlockattr_t) -> c_int {
    unsafe { core::ptr::drop_in_place(attr.cast::<RwlockAttr>()) };
    0
}
