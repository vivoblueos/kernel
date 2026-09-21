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

//! Retirement cleanups that cannot run where the scheduler reaches them.
//!
//! A cleanup may run application code — a pthread's drops POSIX thread-specific
//! data and, for a dynamic application, the reloaded libc's allocator reaches
//! the kernel with an `svc` to hand the thread's stack back — or it may only
//! touch kernel state, as a CMSIS thread's does when it releases a stack the
//! kernel allocated. What they have in common is where the scheduler finds
//! them: from the context-switch path, where interrupts are off, the switch has
//! already published the next thread, and issuing a supervisor call is not
//! defined.
//!
//! Posting is therefore a neutral facility, not an application one: whoever
//! installs a cleanup in `Entry` posts here, and whichever thread will run them
//! drains. The application reaper does that today.
//!
//! Nothing in this module frees anything. It moves the *timing* of a cleanup to
//! a context where the cleanup is allowed to do whatever it does.

use crate::{
    sync::{atomic_wake, spinlock::SpinLock},
    thread::Entry,
};
use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};

/// A posted cleanup.
///
/// `Entry` holds a `Box<dyn FnOnce()>` and raw pointers, so it is neither
/// `Send` nor `Sync`. The queue only carries an entry from the core that
/// retires a thread to the reaper, and the reaper is its only consumer: no
/// other thread ever observes an entry after it is posted, and the reaper
/// owns it outright once it is popped.
struct Deferred(Entry);

unsafe impl Send for Deferred {}
unsafe impl Sync for Deferred {}

/// Cleanups posted by retiring threads.
///
/// The producers run in the context-switch path with interrupts disabled, so
/// the queue is taken with the interrupt-saving lock rather than a plain one.
static QUEUE: SpinLock<Vec<Deferred>> = SpinLock::new(Vec::new());

/// Bumped whenever something the reaper waits for changes: a posted cleanup,
/// or a group newly registered for reaping. Waiting on this address is what
/// lets the reaper notice new work without waiting out its poll bound.
static GENERATION: AtomicUsize = AtomicUsize::new(0);

/// The value to wait on, and the address to wait at.
///
/// Load the generation *before* inspecting the queue or the pending groups: a
/// post that lands mid-scan then moves the value the following wait compares
/// against, instead of being slept through.
pub fn generation() -> usize {
    GENERATION.load(Ordering::Acquire)
}

/// The wait address paired with [`generation`].
pub fn wait_address() -> &'static AtomicUsize {
    &GENERATION
}

/// Wake the reaper without posting work.
///
/// Only call this from a context that may take scheduler and wait-list locks.
/// Producers running in the context-switch path use [`defer`] instead.
pub fn notify() {
    GENERATION.fetch_add(1, Ordering::Release);
    let _ = atomic_wake(&GENERATION, usize::MAX);
}

/// Post `entry` for the reaper to run.
///
/// A retiring thread has no way to fail, so an entry given to this function is
/// never dropped: it either runs or is still in the queue.
///
/// This runs in the context-switch path, so it only queues and advances the
/// generation. Waking a waiter walks the global wait list and re-queues the
/// woken thread, which is more than the switch path should do; the reaper's
/// poll bound is what makes it observe the post, and a wake is not needed for
/// correctness because `atomic_wait` re-checks the generation it was given.
pub fn defer(entry: Entry) {
    QUEUE.irqsave_lock().push(Deferred(entry));
    GENERATION.fetch_add(1, Ordering::Release);
}

/// Run everything posted so far.
///
/// The entries are taken under the lock and invoked after it is released: they
/// run application code, which must not execute with interrupts disabled or
/// while the queue is held.
pub fn drain() {
    let posted = {
        let mut queue = QUEUE.irqsave_lock();
        core::mem::take(&mut *queue)
    };
    for entry in posted {
        match entry.0 {
            Entry::C(f) => f(),
            Entry::Posix(f, arg) => f(arg),
            Entry::Closure(f) => f(),
            // A raw entry is an initial-PC primitive, never a cleanup
            // callback.
            Entry::Raw(..) => debug_assert!(false, "raw entry installed as cleanup"),
        }
    }
}
