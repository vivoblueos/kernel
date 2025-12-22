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

use crate::{
    config,
    scheduler,
    sync::spinlock::SpinLock,
    thread::{self, Entry, SystemThreadStorage, Thread, ThreadKind, ThreadNode},
    time,
};
use alloc::{collections::BTreeSet, vec::Vec};
use blueos_kconfig::TICKS_PER_SECOND;
use core::{
    mem::MaybeUninit,
    sync::atomic::{AtomicBool, AtomicI32, Ordering},
};
use libc::{c_int, c_long, clockid_t, itimerspec, sigevent, time_t, timer_t, timespec, EINVAL};

pub const TIMER_ABSTIME: c_int = 1;
const NS_PER_SEC: i64 = 1_000_000_000;
const NS_PER_MS: u64 = 1_000_000;

pub(crate) const CLOCK_REALTIME: clockid_t = 0;
pub(crate) const CLOCK_MONOTONIC: clockid_t = 1;
pub(crate) const CLOCK_PROCESS_CPUTIME_ID: clockid_t = 2;
pub(crate) const CLOCK_THREAD_CPUTIME_ID: clockid_t = 3;

static REALTIME_OFFSET_NS: SpinLock<i64> = SpinLock::new(0);

type PosixTimerId = i32;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct TimerKey {
    owner_tid: usize,
    local_id: PosixTimerId,
}

impl TimerKey {
    const fn new(owner_tid: usize, local_id: PosixTimerId) -> Self {
        Self { owner_tid, local_id }
    }

    fn hash(self) -> usize {
        let local_part = (self.local_id as u32) as u64;
        let combined = (self.owner_tid as u64) ^ (local_part << 32);
        let mut x = combined.wrapping_mul(0x9E37_79B1_85EB_CA87);
        x ^= x >> 33;
        x = x.wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
        (x ^ (x >> 29)) as usize
    }
}

static NEXT_TIMER_ID: AtomicI32 = AtomicI32::new(1);
static POSIX_TIMER_STORE: SpinLock<PosixTimerStore> =
    SpinLock::const_new(PosixTimerStore::new());


// TODO: posix timer should be trigger in an interrupt handler, for RT PREEMPT kernel, use an work thread
// process them, instead of an threaded interrupt context, and the timer should be sort by expiration time
static POSIX_TIMER_WORKER_READY: AtomicBool = AtomicBool::new(false);
static POSIX_TIMER_WORKER_INIT_GUARD: SpinLock<()> = SpinLock::const_new(());
static mut POSIX_TIMER_THREAD: MaybeUninit<ThreadNode> = MaybeUninit::uninit();
static mut POSIX_TIMER_THREAD_STORAGE: SystemThreadStorage =
    SystemThreadStorage::const_new(ThreadKind::PosixTimer);

struct PosixTimer {
    id: PosixTimerId,
    clock_id: clockid_t,
    interval_ns: i64,
    next_expiration_ns: i64,
    overrun: i32,
    active: bool,
    scheduled_expiration_ns: Option<i64>,
}

impl PosixTimer {
    fn new(id: PosixTimerId, clock_id: clockid_t) -> Self {
        Self {
            id,
            clock_id,
            interval_ns: 0,
            next_expiration_ns: 0,
            overrun: 0,
            active: false,
            scheduled_expiration_ns: None,
        }
    }

    fn disarm(&mut self) {
        self.active = false;
        self.next_expiration_ns = 0;
    }
}

struct TimerSlot {
    key: TimerKey,
    value: PosixTimer,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ExpirationEntry {
    next_expiration_ns: i64,
    key: TimerKey,
}

struct TimerHashMap {
    buckets: Vec<Option<TimerSlot>>,
    len: usize,
}

impl TimerHashMap {
    const fn new() -> Self {
        Self {
            buckets: Vec::new(),
            len: 0,
        }
    }

    fn hash(key: TimerKey) -> usize {
        key.hash()
    }

    fn capacity(&self) -> usize {
        self.buckets.len()
    }

    fn ensure_capacity(&mut self) {
        if self.buckets.is_empty() {
            self.resize(8);
            return;
        }
        if self.len * 4 >= self.capacity() * 3 {
            self.resize(self.capacity() * 2);
        }
    }

    fn resize(&mut self, new_capacity: usize) {
        let mut buckets = Vec::with_capacity(new_capacity);
        buckets.resize_with(new_capacity, || None);
        let old = core::mem::take(&mut self.buckets);
        self.buckets = buckets;
        let old_len = self.len;
        self.len = 0;
        for slot in old.into_iter().flatten() {
            self.insert_entry(slot);
        }
        debug_assert_eq!(self.len, old_len);
        self.len = old_len;
    }

    fn insert(&mut self, key: TimerKey, value: PosixTimer) -> Option<PosixTimer> {
        self.ensure_capacity();
        self.insert_entry(TimerSlot { key, value })
    }

    fn insert_entry(&mut self, entry: TimerSlot) -> Option<PosixTimer> {
        if self.buckets.is_empty() {
            self.resize(8);
        }
        let mask = self.buckets.len() - 1;
        let mut idx = Self::hash(entry.key) & mask;
        let mut entry = Some(entry);
        loop {
            match &mut self.buckets[idx] {
                Some(slot) if slot.key == entry.as_ref().unwrap().key => {
                    let mut slot_entry = entry.take().unwrap();
                    core::mem::swap(slot, &mut slot_entry);
                    return Some(slot_entry.value);
                }
                Some(_) => {
                    idx = (idx + 1) & mask;
                }
                None => {
                    self.buckets[idx] = entry.take();
                    self.len += 1;
                    return None;
                }
            }
        }
    }

    fn get(&self, key: TimerKey) -> Option<&PosixTimer> {
        self.find_slot_index(key)
            .and_then(|idx| self.buckets[idx].as_ref().map(|slot| &slot.value))
    }

    fn get_mut(&mut self, key: TimerKey) -> Option<&mut PosixTimer> {
        let idx = self.find_slot_index(key)?;
        self.buckets[idx]
            .as_mut()
            .map(|slot| &mut slot.value)
    }

    fn find_slot_index(&self, key: TimerKey) -> Option<usize> {
        if self.buckets.is_empty() {
            return None;
        }
        let mask = self.buckets.len() - 1;
        let mut idx = Self::hash(key) & mask;
        loop {
            match &self.buckets[idx] {
                Some(slot) if slot.key == key => return Some(idx),
                Some(_) => idx = (idx + 1) & mask,
                None => return None,
            }
        }
    }

    fn remove(&mut self, key: TimerKey) -> Option<PosixTimer> {
        if self.buckets.is_empty() {
            return None;
        }
        let mask = self.buckets.len() - 1;
        let mut idx = Self::hash(key) & mask;
        loop {
            match self.buckets[idx].take() {
                Some(slot) if slot.key == key => {
                    self.len -= 1;
                    let removed = slot.value;
                    self.reinsert_cluster((idx + 1) & mask);
                    return Some(removed);
                }
                Some(slot) => {
                    self.buckets[idx] = Some(slot);
                    idx = (idx + 1) & mask;
                }
                None => return None,
            }
        }
    }

    fn reinsert_cluster(&mut self, mut idx: usize) {
        if self.buckets.is_empty() {
            return;
        }
        let mask = self.buckets.len() - 1;
        while let Some(slot) = self.buckets[idx].take() {
            self.len -= 1;
            self.insert_entry(slot);
            idx = (idx + 1) & mask;
        }
    }
}
// TODO: it's not an efficient implementation, the posix timer  
// migrate on cpu if system is SMP, so the timer should has an link to per cpu store
struct PosixTimerStore {
    timers: TimerHashMap,
    expirations: BTreeSet<ExpirationEntry>,
}

impl PosixTimerStore {
    const fn new() -> Self {
        Self {
            timers: TimerHashMap::new(),
            expirations: BTreeSet::new(),
        }
    }

    fn schedule_timer(&mut self, key: TimerKey) {
        let Some(timer) = self.timers.get_mut(key) else {
            return;
        };
        if !timer.active {
            timer.scheduled_expiration_ns = None;
            return;
        }
        let entry = ExpirationEntry {
            next_expiration_ns: timer.next_expiration_ns,
            key,
        };
        timer.scheduled_expiration_ns = Some(entry.next_expiration_ns);
        let inserted = self.expirations.insert(entry);
        debug_assert!(inserted, "Timer already scheduled");
    }

    fn deactivate_timer(&mut self, key: TimerKey) {
        let timers = &mut self.timers;
        let expirations = &mut self.expirations;
        if let Some(timer) = timers.get_mut(key) {
            if timer.active {
                remove_scheduled_entry(expirations, key, timer);
                timer.disarm();
            }
        }
    }

    fn allocate_id(&mut self, owner_tid: usize) -> PosixTimerId {
        loop {
            let id = NEXT_TIMER_ID.fetch_add(1, Ordering::Relaxed);
            if id <= 0 {
                NEXT_TIMER_ID.store(1, Ordering::Relaxed);
                continue;
            }
            let key = TimerKey::new(owner_tid, id);
            if self.timers.get(key).is_none() {
                return id;
            }
        }
    }

    fn process_expired_timers(&mut self) -> Option<i64> {
        loop {
            let next_entry = self.expirations.iter().next().cloned()?;
            let action = {
                let timer = match self.timers.get_mut(next_entry.key) {
                    Some(timer) => timer,
                    None => {
                        self.expirations.remove(&next_entry);
                        continue;
                    }
                };

                if !timer.active
                    || timer.scheduled_expiration_ns != Some(next_entry.next_expiration_ns)
                {
                    timer.scheduled_expiration_ns = None;
                    TimerScheduleAction::RemoveOnly
                } else {
                    match current_time_ns_for_clock(timer.clock_id) {
                        Ok(now) => {
                            let remaining = timer.next_expiration_ns.saturating_sub(now);
                            if remaining > 0 {
                                return Some(remaining);
                            }
                            timer.scheduled_expiration_ns = None;
                            handle_timer_fire_locked(timer, now);
                            if timer.active {
                                TimerScheduleAction::RemoveAndSchedule
                            } else {
                                TimerScheduleAction::RemoveOnly
                            }
                        }
                        Err(_) => {
                            timer.scheduled_expiration_ns = None;
                            timer.disarm();
                            TimerScheduleAction::RemoveOnly
                        }
                    }
                }
            };

            self.expirations.remove(&next_entry);
            if let TimerScheduleAction::RemoveAndSchedule = action {
                self.schedule_timer(next_entry.key);
            }
        }
    }
}

fn remove_scheduled_entry(
    expirations: &mut BTreeSet<ExpirationEntry>,
    key: TimerKey,
    timer: &mut PosixTimer,
) {
    if let Some(expiration) = timer.scheduled_expiration_ns.take() {
        let entry = ExpirationEntry {
            next_expiration_ns: expiration,
            key,
        };
        expirations.remove(&entry);
    }
}

enum TimerScheduleAction {
    RemoveOnly,
    RemoveAndSchedule,
}

// user will pass pointer size timer_t ?
fn timer_id_from_user(timerid: timer_t) -> PosixTimerId {
    timerid as usize as PosixTimerId
}

fn timer_id_to_user(id: PosixTimerId) -> timer_t {
    (id as usize) as timer_t
}

fn timer_key_for_current_thread(id: PosixTimerId) -> TimerKey {
    TimerKey::new(scheduler::current_thread_id(), id)
}

fn current_time_ns_for_clock(clock_id: clockid_t) -> Result<i64, c_long> {
    match clock_id {
        CLOCK_REALTIME => Ok(realtime_time_ns()),
        CLOCK_MONOTONIC => Ok(monotonic_time_ns()),
        _ => Err(-EINVAL as c_long),
    }
}

fn disarm_timer(timer: &mut PosixTimer) {
    timer.disarm();
}

fn arm_timer(timer: &mut PosixTimer, delay_ns: i64) -> Result<(), c_long> {
    if delay_ns <= 0 {
        disarm_timer(timer);
        return Ok(());
    }
    let now = current_time_ns_for_clock(timer.clock_id)?;
    timer.next_expiration_ns = now.saturating_add(delay_ns);
    timer.active = true;
    Ok(())
}

fn remaining_time_ns(timer: &PosixTimer) -> Result<i64, c_long> {
    if !timer.active {
        return Ok(0);
    }
    let now = current_time_ns_for_clock(timer.clock_id)?;
    Ok(timer.next_expiration_ns.saturating_sub(now))
}

fn write_itimerspec(timer: &PosixTimer, dest: *mut itimerspec) -> Result<(), c_long> {
    if dest.is_null() {
        return Ok(());
    }
    let remaining = remaining_time_ns(timer)?.max(0);
    unsafe {
        (*dest).it_interval = ns_to_timespec(timer.interval_ns.max(0));
        (*dest).it_value = ns_to_timespec(remaining);
    }
    Ok(())
}

// TODO: queue the signal 
fn handle_timer_fire_locked(timer: &mut PosixTimer, now_ns: i64) {
    timer.overrun = timer.overrun.saturating_add(1);
    if timer.interval_ns > 0 {
        let mut next = timer.next_expiration_ns.saturating_add(timer.interval_ns);
        while next <= now_ns {
            next = next.saturating_add(timer.interval_ns);
        }
        timer.next_expiration_ns = next;
        timer.active = true;
    } else {
        timer.disarm();
    }
}

fn ensure_posix_timer_worker() {
    if POSIX_TIMER_WORKER_READY.load(Ordering::Acquire) {
        return;
    }
    let _guard = POSIX_TIMER_WORKER_INIT_GUARD.lock();
    if POSIX_TIMER_WORKER_READY.load(Ordering::Acquire) {
        return;
    }
    let thread = thread::build_static_thread(
        unsafe { &mut POSIX_TIMER_THREAD },
        unsafe { &mut POSIX_TIMER_THREAD_STORAGE },
        config::POSIX_TIMER_THREAD_PRIORITY,
        thread::CREATED,
        Entry::C(run_posix_timer_worker),
        ThreadKind::PosixTimer,
    );
    unsafe { POSIX_TIMER_THREAD.write(thread.clone()) };
    let ok = scheduler::queue_ready_thread(thread::CREATED, thread);
    debug_assert!(ok);
    POSIX_TIMER_WORKER_READY.store(true, Ordering::Release);
}

fn wake_posix_timer_worker() {
    if !POSIX_TIMER_WORKER_READY.load(Ordering::Acquire) {
        return;
    }
    let thread = unsafe { POSIX_TIMER_THREAD.assume_init_ref() };
    let _ = scheduler::queue_ready_thread(thread::SUSPENDED, thread.clone());
}

extern "C" fn run_posix_timer_worker() {
    loop {
        let next_delay = {
            let mut store = POSIX_TIMER_STORE.lock();
            store.process_expired_timers()
        };
        match next_delay {
            Some(delay) => {
                if delay <= 0 {
                    scheduler::yield_me();
                    continue;
                }
                let ticks = ticks_from_ns(delay);
                if ticks == 0 {
                    scheduler::yield_me();
                } else {
                    scheduler::suspend_me_for(ticks);
                }
            }
            None => {
                scheduler::suspend_me_for(time::WAITING_FOREVER);
            }
        }
    }
}

// add for blueos time type representation in i64 nanoseconds
fn ms_to_ns_saturated(millis: u64) -> i64 {
    let nanos = millis.saturating_mul(NS_PER_MS);
    if nanos > i64::MAX as u64 {
        i64::MAX
    } else {
        nanos as i64
    }
}

fn thread_cpu_cycles(thread: &Thread) -> u64 {
    let mut total = thread.get_cycles();
    if thread.state() == thread::RUNNING {
        let now = time::get_sys_cycles();
        total = total.saturating_add(now.saturating_sub(thread.start_cycles()));
    }
    total
}

fn thread_cpu_time_ns(thread: &Thread) -> i64 {
    let millis = time::cycles_to_millis(thread_cpu_cycles(thread));
    ms_to_ns_saturated(millis)
}

fn current_thread_cpu_time_ns() -> i64 {
    let current = scheduler::current_thread();
    thread_cpu_time_ns(&current)
}

fn current_process_cpu_time_ns() -> i64 {
    // BlueOS currently has no POSIX process, so reuse the
    // calling thread's CPU time as the process-wide accounting.
    current_thread_cpu_time_ns()
}

pub(crate) fn monotonic_time_ns() -> i64 {
    let cycles = time::get_sys_cycles();
    let millis = time::cycles_to_millis(cycles);
    ms_to_ns_saturated(millis)
}

pub(crate) fn realtime_time_ns() -> i64 {
    let offset = *REALTIME_OFFSET_NS.lock();
    monotonic_time_ns().saturating_add(offset)
}

pub(crate) fn set_realtime_offset_ns(offset: i64) {
    *REALTIME_OFFSET_NS.lock() = offset;
}

fn ns_to_timespec(total_ns: i64) -> timespec {
    let mut seconds = total_ns / NS_PER_SEC;
    let mut nanoseconds = total_ns % NS_PER_SEC;
    if nanoseconds < 0 {
        seconds -= 1;
        nanoseconds += NS_PER_SEC;
    }
    timespec {
        tv_sec: seconds as time_t,
        tv_nsec: nanoseconds as c_long,
    }
}

fn timespec_to_ns(ts: &timespec) -> Result<i64, c_long> {
    if ts.tv_nsec < 0 || ts.tv_nsec as i64 >= NS_PER_SEC {
        return Err(-EINVAL as c_long);
    }
    let seconds = ts.tv_sec as i64;
    let nanos = ts.tv_nsec as i64;
    seconds
        .checked_mul(NS_PER_SEC)
        .and_then(|base| base.checked_add(nanos))
        .ok_or(-EINVAL as c_long)
}

fn ticks_from_ns(ns: i64) -> usize {
    if ns <= 0 {
        return 0;
    }
    let ticks_per_second = TICKS_PER_SECOND as i64;
    let seconds = ns / NS_PER_SEC;
    let nanos = ns % NS_PER_SEC;

    let ticks_from_seconds = seconds.saturating_mul(ticks_per_second);
    let fractional = (nanos
        .saturating_mul(ticks_per_second)
        .saturating_add(NS_PER_SEC - 1))
        / NS_PER_SEC;

    let total = ticks_from_seconds.saturating_add(fractional);
    match usize::try_from(total) {
        Ok(val) => val,
        Err(_) => usize::MAX,
    }
}

fn sleep_for_ticks(ticks: usize) {
    if ticks == 0 {
        scheduler::yield_me();
    } else {
        scheduler::suspend_me_for(ticks);
    }
}

pub(crate) fn is_supported_clock_id(clock_id: clockid_t) -> bool {
    matches!(
        clock_id,
        CLOCK_REALTIME | CLOCK_MONOTONIC | CLOCK_PROCESS_CPUTIME_ID | CLOCK_THREAD_CPUTIME_ID
    )
}

pub(crate) fn clock_gettime(clk_id: clockid_t, tp: *mut timespec) -> c_long {
    if tp.is_null() {
        return -EINVAL as c_long;
    }
    if !is_supported_clock_id(clk_id) {
        return -EINVAL as c_long;
    }
    let time_ns: i64 = match clk_id {
    CLOCK_REALTIME => realtime_time_ns(),
    CLOCK_MONOTONIC => monotonic_time_ns(),
    CLOCK_PROCESS_CPUTIME_ID => current_process_cpu_time_ns(),
    CLOCK_THREAD_CPUTIME_ID => current_thread_cpu_time_ns(),
    _ => monotonic_time_ns(),
    };
    unsafe {
        *tp = ns_to_timespec(time_ns);
    }
    0
}

// don't allow set CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID, CLOCK_THREAD_CPUTIME_ID
pub(crate) fn clock_settime(clk_id: clockid_t, tp: *const timespec) -> c_long {
    if tp.is_null() {
        return -EINVAL as c_long;
    }
    if clk_id != CLOCK_REALTIME {
        return -EINVAL as c_long;
    }
    let requested = unsafe { &*tp };
    let target_ns = match timespec_to_ns(requested) {
        Ok(ns) => ns,
        Err(errno) => return errno,
    };
    let monotonic_ns = monotonic_time_ns();
    set_realtime_offset_ns(target_ns.saturating_sub(monotonic_ns));
    0
}

fn validate_clock_for_sleep(clock_id: clockid_t) -> bool {
    matches!(clock_id, CLOCK_MONOTONIC | CLOCK_REALTIME)
}

fn remaining_ns_for_absolute(clock_id: clockid_t, target: &timespec) -> Result<i64, c_long> {
    let target_ns = timespec_to_ns(target)?;
    let now_ns = match clock_id {
        CLOCK_REALTIME => realtime_time_ns(),
        CLOCK_MONOTONIC => monotonic_time_ns(),
        _ => return Err(-EINVAL as c_long),
    };
    Ok(target_ns.saturating_sub(now_ns))
}

fn remaining_ns_for_relative(target: &timespec) -> Result<i64, c_long> {
    let ns = timespec_to_ns(target)?;
    if ns < 0 {
        return Err(-EINVAL as c_long);
    }
    Ok(ns)
}

fn clear_remaining_time(rmtp: *mut timespec) {
    if rmtp.is_null() {
        return;
    }
    unsafe {
        (*rmtp).tv_sec = 0;
        (*rmtp).tv_nsec = 0;
    }
}

pub(crate) fn clock_nanosleep(
    clock_id: clockid_t,
    flags: c_int,
    rqtp: *const timespec,
    rmtp: *mut timespec,
) -> c_long {
    if rqtp.is_null() {
        return -EINVAL as c_long;
    }
    if !validate_clock_for_sleep(clock_id) {
        return -EINVAL as c_long;
    }
    let supported_flags = TIMER_ABSTIME;
    if flags & !supported_flags != 0 {
        return -EINVAL as c_long;
    }
    let request = unsafe { &*rqtp };
    let remaining_ns = if (flags & TIMER_ABSTIME) != 0 {
        remaining_ns_for_absolute(clock_id, request)
    } else {
        remaining_ns_for_relative(request)
    };
    let remaining_ns = match remaining_ns {
        Ok(ns) => ns,
        Err(errno) => return errno,
    };
    if remaining_ns <= 0 {
        clear_remaining_time(rmtp);
        return 0;
    }
    let ticks = ticks_from_ns(remaining_ns);
    sleep_for_ticks(ticks);
    clear_remaining_time(rmtp);
    0
}

pub(crate) fn timer_create(
    clock_id: clockid_t,
    evp: *const sigevent,
    timerid: *mut timer_t,
) -> c_long {
    if timerid.is_null() {
        return -EINVAL as c_long;
    }
    if !matches!(clock_id, CLOCK_REALTIME | CLOCK_MONOTONIC) {
        return -EINVAL as c_long;
    }
    if !evp.is_null() {
        // Custom sigevent delivery is not supported yet.
        return -EINVAL as c_long;
    }
    ensure_posix_timer_worker();
    let mut store = POSIX_TIMER_STORE.lock();
    let owner_tid = scheduler::current_thread_id();
    let id = store.allocate_id(owner_tid);
    let posix_timer = PosixTimer::new(id, clock_id);
    let key = TimerKey::new(owner_tid, id);
    store.timers.insert(key, posix_timer);
    unsafe {
        *timerid = timer_id_to_user(id);
    }
    0
}

pub(crate) fn timer_delete(timerid: timer_t) -> c_long {
    let id = timer_id_from_user(timerid);
    let key = timer_key_for_current_thread(id);
    let mut store = POSIX_TIMER_STORE.lock();
    match store.timers.remove(key) {
        Some(mut timer) => {
            remove_scheduled_entry(&mut store.expirations, key, &mut timer);
            timer.disarm();
            drop(store);
            wake_posix_timer_worker();
            0
        }
        None => -EINVAL as c_long,
    }
}

pub(crate) fn timer_getoverrun(timerid: timer_t) -> c_long {
    let id = timer_id_from_user(timerid);
    let key = timer_key_for_current_thread(id);
    let mut store = POSIX_TIMER_STORE.lock();
    match store.timers.get_mut(key) {
        Some(timer) => {
            let value = timer.overrun as c_long;
            timer.overrun = 0;
            value
        }
        None => -EINVAL as c_long,
    }
}

pub(crate) fn timer_gettime(timerid: timer_t, value: *mut itimerspec) -> c_long {
    if value.is_null() {
        return -EINVAL as c_long;
    }
    let id = timer_id_from_user(timerid);
    let key = timer_key_for_current_thread(id);
    let store = POSIX_TIMER_STORE.lock();
    match store.timers.get(key) {
        Some(timer) => match write_itimerspec(timer, value) {
            Ok(()) => 0,
            Err(errno) => errno,
        },
        None => -EINVAL as c_long,
    }
}

pub(crate) fn timer_settime(
    timerid: timer_t,
    flags: c_int,
    value: *const itimerspec,
    ovalue: *mut itimerspec,
) -> c_long {
    if value.is_null() {
        return -EINVAL as c_long;
    }
    if flags & !TIMER_ABSTIME != 0 {
        return -EINVAL as c_long;
    }
    let id = timer_id_from_user(timerid);
    let key = timer_key_for_current_thread(id);
    let mut store = POSIX_TIMER_STORE.lock();
    let clock_id = {
        let timer = match store.timers.get_mut(key) {
            Some(timer) => timer,
            None => return -EINVAL as c_long,
        };

        if let Err(errno) = write_itimerspec(timer, ovalue) {
            return errno;
        }
        timer.clock_id
    };

    store.deactivate_timer(key);

    let spec = unsafe { &*value };
    let interval_ns = match timespec_to_ns(&spec.it_interval) {
        Ok(ns) if ns >= 0 => ns,
        _ => return -EINVAL as c_long,
    };
    let initial_ns = match timespec_to_ns(&spec.it_value) {
        Ok(ns) if ns >= 0 => ns,
        _ => return -EINVAL as c_long,
    };

    {
        let timer = match store.timers.get_mut(key) {
            Some(timer) => timer,
            None => return -EINVAL as c_long,
        };
        timer.interval_ns = interval_ns;
        timer.overrun = 0;
    }

    if initial_ns == 0 {
        drop(store);
        wake_posix_timer_worker();
        return 0;
    }

    let delay_ns = if (flags & TIMER_ABSTIME) != 0 {
        match current_time_ns_for_clock(clock_id) {
            Ok(now) => initial_ns.saturating_sub(now),
            Err(errno) => return errno,
        }
    } else {
        initial_ns
    };

    if delay_ns <= 0 {
        drop(store);
        wake_posix_timer_worker();
        return 0;
    }

    let arm_result = {
        let timer = match store.timers.get_mut(key) {
            Some(timer) => timer,
            None => return -EINVAL as c_long,
        };
        arm_timer(timer, delay_ns)
    };

    match arm_result {
        Ok(()) => {
            store.schedule_timer(key);
            drop(store);
            wake_posix_timer_worker();
            0
        }
        Err(errno) => errno,
    }
}
