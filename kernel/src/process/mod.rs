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

use crate::{
    scheduler,
    sync::SpinLock,
    thread::{Thread, ThreadList, ThreadNode},
};
use alloc::sync::{Arc, Weak};

#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pid(pub u32);

/// The process that owns the currently running thread, if any.
///
/// Returns `None` for kernel/idle threads (whose `process` weak reference is
/// dangling). Only valid after [`scheduler::init`] has populated the per-CPU
/// `RUNNING_THREADS`; calling it earlier reads uninitialized memory.
///
/// Kernel code that needs a file should grab the file's struct directly rather
/// than going through an fd — there is no "kernel process" whose table backs
/// such operations.
#[inline]
pub fn current_process() -> Option<Arc<Process>> {
    scheduler::current_thread_ref().process()
}

pub struct Process {
    pid: Pid,
    // A weak reference to the parent process.
    parent: Weak<Process>,
    // The threads owned by this process.
    threads: SpinLock<ThreadList>,
}

impl Process {
    pub fn new(pid: Pid, parent: Weak<Process>) -> Self {
        let mut s = Self {
            pid,
            parent,
            threads: SpinLock::new(ThreadList::new()),
        };
        s.threads.irqsave_lock().init();
        s
    }

    /// Create the root process, whose `parent` points to itself.
    pub fn new_root(pid: Pid) -> Arc<Self> {
        let root = Arc::new_cyclic(|weak_self| Self {
            pid,
            parent: weak_self.clone(),
            threads: SpinLock::new(ThreadList::new()),
        });
        // SAFETY: `root` is the sole strong reference at this point (the
        // self-referential `weak_self` cloned into `parent` is a `Weak`, which
        // does not hold a strong count). `new_root` has not returned the Arc to
        // any caller yet, so no other thread can observe it. Mutating the
        // `threads` field through a raw pointer is therefore sound.
        unsafe {
            Arc::as_ptr(&root)
                .cast_mut()
                .as_mut()
                .unwrap()
                .threads
                .irqsave_lock()
                .init();
        }
        root
    }

    pub fn pid(&self) -> Pid {
        self.pid
    }

    pub fn parent(&self) -> Option<Arc<Process>> {
        self.parent.upgrade()
    }

    /// Add a thread to this process's thread list.
    ///
    /// Returns `true` when success, and `false` if the thread was already
    /// linked into another process's thread list.
    pub fn add_thread(self: &Arc<Self>, thread: ThreadNode) -> bool {
        let weak = Arc::downgrade(self);
        let mut list = self.threads.irqsave_lock();
        if !list.push_back(thread) {
            return false;
        }
        if let Some(t) = list.back() {
            t.lock().set_process(weak);
        }
        true
    }

    /// Detach a thread from this process's thread list.
    ///
    /// Returns `false` if the thread is not currently linked to this process.
    pub fn remove_thread(&self, thread: &mut ThreadNode) -> bool {
        let _guard = self.threads.irqsave_lock();
        let removed = ThreadList::detach(thread);
        if removed {
            thread.lock().set_process(Weak::new());
        }
        removed
    }

    pub fn has_no_threads(&self) -> bool {
        self.threads.irqsave_lock().is_empty()
    }

    pub fn thread_count(&self) -> usize {
        self.threads.irqsave_lock().iter().count()
    }

    /// Invoke `f` for every thread owned by this process.
    ///
    /// The process's thread list lock is held for the duration of the call,
    /// so `f` must not recursively lock the same list. Thread references
    /// obtained through `f` are invalidated once `f` returns, since the lock
    /// is dropped.
    pub fn for_each_thread<F: FnMut(&Thread)>(&self, mut f: F) {
        let list = self.threads.irqsave_lock();
        for t in list.iter() {
            f(t);
        }
    }
}

impl core::fmt::Debug for Process {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let parent_pid = self.parent.upgrade().map(|p| p.pid());
        f.debug_struct("Process")
            .field("pid", &self.pid)
            .field("parent", &parent_pid)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use blueos_test_macro::test;

    #[test]
    fn process_basic() {
        // Root process (pid 0); its parent is itself via new_cyclic.
        let root = Process::new_root(Pid(0));
        assert_eq!(root.pid(), Pid(0));
        // Root's parent upgrades to an Arc whose pid is itself.
        assert_eq!(root.parent().map(|p| p.pid()), Some(Pid(0)));

        // A child (pid 1) whose parent is root.
        let child = Process::new(Pid(1), Arc::downgrade(&root));
        assert_eq!(child.pid(), Pid(1));
        assert_eq!(child.parent().map(|p| p.pid()), Some(Pid(0)));
    }

    #[test]
    fn process_dropped_parent() {
        // When the parent Arc is dropped, upgrade returns None.
        let weak = {
            let parent = Arc::new(Process::new(Pid(0), Weak::new()));
            Arc::downgrade(&parent)
        };
        let child = Process::new(Pid(1), weak);
        assert!(child.parent().is_none());
    }

    #[test]
    fn process_starts_with_no_threads() {
        // A freshly created process owns no threads.
        let root = Process::new_root(Pid(0));
        assert!(root.has_no_threads());
        assert_eq!(root.thread_count(), 0);
    }
}
