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

#[cfg(enable_vfs)]
use crate::vfs::fd_manager::FdManager;
use crate::{
    error::Error,
    mm::address_space::AddressSpace,
    scheduler,
    sync::SpinLock,
    thread::{Thread, ThreadList, ThreadNode},
};
use alloc::{
    collections::BTreeMap,
    sync::{Arc, Weak},
};
use core::sync::atomic::{AtomicU32, Ordering};
use spin::Once;

#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pid(pub u32);

pub const ROOT_PID: Pid = Pid(1);

#[inline]
pub fn current_process() -> Option<Arc<Process>> {
    scheduler::current_thread_ref().process()
}

pub struct ProcessTable {
    table: SpinLock<BTreeMap<Pid, Arc<Process>>>,
}

impl ProcessTable {
    pub const fn new() -> Self {
        Self {
            table: SpinLock::new(BTreeMap::new()),
        }
    }

    pub fn insert(&self, process: Arc<Process>) -> Arc<Process> {
        let mut t = self.table.irqsave_lock();
        let pid = process.pid();
        assert!(
            t.insert(pid, Arc::clone(&process)).is_none(),
            "duplicate pid {:?} in process table",
            pid,
        );
        process
    }

    pub fn get(&self, pid: Pid) -> Option<Arc<Process>> {
        self.table.irqsave_lock().get(&pid).cloned()
    }

    /// Remove a process from the table, dropping the table's strong ref.
    /// `None` if the pid was absent.
    pub fn remove(&self, pid: Pid) -> Option<Arc<Process>> {
        self.table.irqsave_lock().remove(&pid)
    }
}

pub struct ProcessManager {
    next_pid: AtomicU32,
    root: Arc<Process>,
    table: ProcessTable,
}

impl ProcessManager {
    fn new() -> Self {
        let root = Process::new(ROOT_PID, Weak::new()).expect("create root process failed!");
        let manager = Self {
            next_pid: AtomicU32::new(2),
            root: root.clone(),
            table: ProcessTable::new(),
        };
        manager.table.insert(root);
        manager
    }

    #[inline]
    pub fn get() -> &'static ProcessManager {
        PROCESS_MANAGER.call_once(Self::new)
    }

    pub fn root_process(&'static self) -> &'static Arc<Process> {
        &self.root
    }

    #[inline]
    pub fn process_table(&self) -> &ProcessTable {
        &self.table
    }

    pub fn create_process(&self, parent: Weak<Process>) -> Result<Arc<Process>, Error> {
        let pid = self.alloc_pid();
        let process = Process::new(pid, parent.clone())?;
        let inserted = self.table.insert(process);
        if let Some(parent_arc) = parent.upgrade() {
            parent_arc.add_child(inserted.pid(), Arc::downgrade(&inserted));
        }
        Ok(inserted)
    }

    pub fn destroy_process(&self, pid: Pid) -> Option<Arc<Process>> {
        if pid == ROOT_PID {
            return None;
        }
        let proc = self.table.get(pid)?;
        let st = proc.state();
        match st {
            ProcessState::Alive => {
                proc.become_zombie();
                if proc.has_no_threads() {
                    return self.finalize_destroy(&proc);
                }
                None
            }
            ProcessState::Zombie => {
                if proc.has_no_threads() {
                    return self.finalize_destroy(&proc);
                }
                None
            }
            ProcessState::Dead => None,
        }
    }

    pub(crate) fn finalize_destroy(&self, proc: &Arc<Process>) -> Option<Arc<Process>> {
        let removed = self.table.remove(proc.pid());
        let p = removed.as_ref()?;
        if let Some(parent) = p.parent() {
            parent.remove_child(p.pid());
        }
        if p.pid() != ROOT_PID {
            reparent_orphans_to_root(&self.root, p);
        }
        // TODO: release AddressSpace resource
        p.become_dead();
        removed
    }

    pub fn alloc_pid(&self) -> Pid {
        let pid = self
            .next_pid
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |prev| {
                self.next_pid(prev)
            })
            .expect("no available pid");
        assert!(
            pid != 0 && pid != ROOT_PID.0,
            "alloc_pid invariant violated"
        );
        Pid(pid)
    }

    pub fn next_pid(&self, prev: u32) -> Option<u32> {
        let mut candidate = prev;
        loop {
            candidate = match candidate.checked_add(1) {
                None | Some(0) | Some(1) => 2,
                Some(v) => v,
            };
            if candidate == prev {
                return None;
            }
            if self.table.get(Pid(candidate)).is_none() {
                return Some(candidate);
            }
        }
    }
}

static PROCESS_MANAGER: Once<ProcessManager> = Once::new();

/// Reparent `proc`'s surviving children to `root` (the init/reaper process).
#[inline(never)]
fn reparent_orphans_to_root(root: &Arc<Process>, proc_: &Process) {
    let orphans: alloc::vec::Vec<Arc<Process>> = {
        let mut v = alloc::vec::Vec::new();
        proc_.for_each_child(|c| v.push(Arc::clone(c)));
        v
    };
    for child in orphans {
        proc_.remove_child(child.pid());
        child.set_parent(Arc::downgrade(root));
        root.add_child(child.pid(), Arc::downgrade(&child));
    }
}

/// Lifecycle state of a process
///
/// - `Alive`: created, may own threads, findable in the table and parent.
/// - `Zombie`: teardown requested but threads still survive; still in the
///   table and parent so the threads' `Weak<Process>` keeps resolving.
/// - `Dead`: reclamation complete; removed from the table and parent. Only
///   observable via the `Arc<Process>` returned by `destroy_process` (or held
///   by a caller) before it is dropped.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProcessState {
    Alive,
    Zombie,
    Dead,
}

/// Parent/child topology of a process.
struct ProcessTopology {
    // Weak back-pointer to the parent process.
    parent: Weak<Process>,
    // Children of this process: Pid -> Weak<Process>.
    children: BTreeMap<Pid, Weak<Process>>,
    // Lifecycle state. Read under `irqsave_read()`,
    state: ProcessState,
}

pub struct Process {
    pid: Pid,
    // Parent/child topology. Read with `irqsave_read()`, mutate with
    // `irqsave_write()`. Never hold two processes' topology locks at once
    // (see `ProcessManager::create_process`/`destroy_process`).
    topology: SpinLock<ProcessTopology>,
    // The threads owned by this process.
    threads: SpinLock<ThreadList>,
    // This process's independent address space
    address_space: Arc<AddressSpace>,
    // This process's open-file table.
    #[cfg(enable_vfs)]
    fd_manager: SpinLock<FdManager>,
}

// SAFETY: `Process` would otherwise be `!Send` only because `threads` holds a
// `TinyArcList` (whose `AtomicListHead` is deliberately `!Send` since it stores
// a raw `NonNull`). A process never actually migrates across cores by being
// *moved* as a Rust value: once created it is pinned behind an `Arc` whose
// storage is never moved or dropped, and every field that can be touched
// concurrently (`topology`, `threads`, `fd_manager`) is already guarded by a
// `SpinLock` whose irqsave read/write guards serialize access. The remaining
// field (`pid`) is plain `Send + Sync`. So it is sound to move the owning
// `Arc<Process>` between threads and to share `&Process` across cores — which
// the scheduler already relies on for the root process. This unlocks
// `Once<Arc<Process>>` (the `root` field) and `Once<ProcessManager>` as
// `static` storage (both need `T: Send + Sync` for `Sync`).
unsafe impl Send for Process {}
unsafe impl Sync for Process {}

impl Process {
    pub fn new(pid: Pid, parent: Weak<Process>) -> Result<Arc<Self>, crate::error::Error> {
        let arc = Arc::new(Self {
            pid,
            topology: SpinLock::new(ProcessTopology {
                parent,
                children: BTreeMap::new(),
                state: ProcessState::Alive,
            }),
            threads: SpinLock::new(ThreadList::new()),
            address_space: Arc::new(AddressSpace::new()),

            #[cfg(enable_vfs)]
            fd_manager: SpinLock::new(FdManager::new()),
        });
        // SAFETY: `arc` is the sole strong ref and is not yet observable by any
        // other thread, so this `&mut Process` aliases no live reference.
        let p = unsafe { Arc::as_ptr(&arc).cast_mut().as_mut().unwrap() };
        #[cfg(enable_vfs)]
        {
            p.fd_manager.irqsave_lock().init_stdio()?;
        }
        p.threads.irqsave_lock().init();
        Ok(arc)
    }

    pub fn pid(&self) -> Pid {
        self.pid
    }

    pub fn parent(&self) -> Option<Arc<Process>> {
        self.topology.irqsave_read().parent.upgrade()
    }

    /// Set this process's parent pointer
    pub fn set_parent(&self, parent: Weak<Process>) {
        self.topology.irqsave_write().parent = parent;
    }

    /// Current lifecycle state. See [`ProcessState`].
    pub fn state(&self) -> ProcessState {
        self.topology.irqsave_read().state
    }

    /// Transition `Alive -> Zombie`. Returns the *previous* state so a caller
    /// can detect a duplicate/racing destroy request.
    fn become_zombie(&self) -> ProcessState {
        let mut topo = self.topology.irqsave_write();
        let prev = topo.state;
        if prev == ProcessState::Alive {
            topo.state = ProcessState::Zombie;
        }
        prev
    }

    fn become_dead(&self) {
        let mut topo = self.topology.irqsave_write();
        topo.state = ProcessState::Dead;
    }

    /// Look up a child of this process by pid.
    pub fn child(&self, pid: Pid) -> Option<Arc<Process>> {
        let topo = self.topology.irqsave_read();
        topo.children.get(&pid).and_then(|w| w.upgrade())
    }

    /// Number of child processes.
    pub fn child_count(&self) -> usize {
        self.topology.irqsave_read().children.len()
    }

    pub fn has_no_children(&self) -> bool {
        self.topology.irqsave_read().children.is_empty()
    }

    /// Invoke `f` for each child process (as `Arc<Process>`).
    ///
    /// The topology read lock is held for the duration of the call, so `f`
    /// must not recursively take this process's topology write lock.
    pub fn for_each_child<F: FnMut(&Arc<Process>)>(&self, mut f: F) {
        let topo = self.topology.irqsave_read();
        for weak in topo.children.values() {
            if let Some(arc) = weak.upgrade() {
                f(&arc);
            }
        }
    }

    /// Register a child under this process's children map.
    fn add_child(&self, child_pid: Pid, child: Weak<Process>) {
        self.topology
            .irqsave_write()
            .children
            .insert(child_pid, child);
    }

    /// Remove a child entry. Returns the removed weak ref, if any.
    fn remove_child(&self, child_pid: Pid) -> Option<Weak<Process>> {
        self.topology.irqsave_write().children.remove(&child_pid)
    }

    /// This process's open-file table. Only present when VFS is enabled.
    #[cfg(enable_vfs)]
    pub fn fd_manager(&self) -> &SpinLock<FdManager> {
        &self.fd_manager
    }

    /// This process's independent address space.
    pub fn address_space(&self) -> &Arc<AddressSpace> {
        &self.address_space
    }

    /// Add a thread to this process's thread list.
    ///
    /// Returns `true` when success, and `false` when failed.
    pub fn add_thread(self: &Arc<Self>, thread: ThreadNode) -> bool {
        if self.state() != ProcessState::Alive {
            return false;
        }
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
        let parent_pid = self.parent().map(|p| p.pid());
        let mut dbg = f.debug_struct("Process");
        dbg.field("pid", &self.pid)
            .field("parent", &parent_pid)
            .field("address_space", &self.address_space);
        #[cfg(enable_vfs)]
        dbg.field("fd_manager", &"<per-process>");
        dbg.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate as blueos;
    use alloc::{boxed::Box, sync::Arc};
    use blueos_test_macro::test;

    // Entry point for threads that the tests build via `Builder` but never
    // schedule. `Builder::build` stores the entry in the thread's context
    // (return-address + arg slots) but does *not* put it in `cleanup`, so it is
    // only ever invoked if the thread is actually run — which these threads
    // never are. Using `Entry::C` (a plain function pointer, no allocation)
    // instead of `Entry::Closure` avoids leaking a `Box::into_raw`'d closure
    // when such a thread is dropped un-run.
    extern "C" fn never_run_entry() {
        unreachable!("test-only thread must never be scheduled");
    }

    #[test]
    fn process_basic() {
        // Root process (pid `ROOT_PID` = 1)
        let root = Process::new(ROOT_PID, Weak::new()).expect("Process::new failed");
        assert_eq!(root.pid(), ROOT_PID);
        // Root's parent is None.
        assert!(root.parent().is_none());

        // A child whose parent is root. `Pid(0)` is the auto-allocate
        // sentinel — the child gets a fresh PID (>= 2) and never collides
        // with root's `ROOT_PID`. Assert invariants rather than a fixed
        // value, since the global counter is shared across tests.
        let child = Process::new(Pid(2), Arc::downgrade(&root)).expect("Process::new failed");
        assert_ne!(child.pid(), root.pid());
        assert_eq!(child.parent().map(|p| p.pid()), Some(ROOT_PID));

        // Every process is born with an empty, independent address space.
        assert!(root.address_space().is_empty());
        assert!(child.address_space().is_empty());
        // Root and child do not share an address space.
        assert!(!Arc::ptr_eq(root.address_space(), child.address_space()));

        // When VFS is enabled, every process also owns an independent
        // per-process open-file table. The syscall path resolves each
        // process's own table via `current_process()`.
        #[cfg(enable_vfs)]
        {
            // `Process::new` initializes stdio (stdin/stdout/stderr) for every
            // process, so both root and child have 3 fds and `get_file_ops(0)`
            // is `Some`.
            assert_eq!(root.fd_manager().irqsave_lock().count(), 3);
            assert!(root.fd_manager().irqsave_lock().get_file_ops(0).is_some());
            assert_eq!(child.fd_manager().irqsave_lock().count(), 3);
            assert!(child.fd_manager().irqsave_lock().get_file_ops(0).is_some());
            // Root and child do not share a fd table.
            assert!(!core::ptr::eq(
                root.fd_manager() as *const _,
                child.fd_manager() as *const _,
            ));
        }
    }

    #[test]
    fn process_dropped_parent() {
        // When the parent Arc is dropped, upgrade returns None.
        let weak = {
            let parent = Process::new(Pid(0), Weak::new()).expect("Process::new failed");
            Arc::downgrade(&parent)
        };
        let child = Process::new(Pid(0), weak).expect("Process::new failed");
        assert!(child.parent().is_none());
    }

    #[test]
    fn process_starts_with_no_threads() {
        // A freshly created process owns no threads.
        let root = Process::new(ROOT_PID, Weak::new()).expect("Process::new failed");
        assert!(root.has_no_threads());
        assert_eq!(root.thread_count(), 0);
    }

    #[test]
    fn alloc_pid_skips_reserved() {
        // alloc_pid never hands out the auto-allocate sentinel (0) or the
        // root process's reserved `ROOT_PID` (1); each returned value also
        // differs from the previous one (the counter strictly advances,
        // modulo the `u32::MAX` wrap exercised below).
        let a = ProcessManager::get().alloc_pid();
        let b = ProcessManager::get().alloc_pid();
        assert!(
            a != Pid(0) && a != ROOT_PID,
            "alloc_pid never returns 0 or ROOT_PID"
        );
        assert!(b != Pid(0) && b != ROOT_PID);
        assert!(a != b, "alloc_pid returns distinct values");
    }

    #[test]
    fn next_pid_skips_reserved_and_live() {
        let occupied = |pid: u32| {
            pid == 0
                || pid == ROOT_PID.0
                || ProcessManager::get()
                    .process_table()
                    .get(Pid(pid))
                    .is_some()
        };

        for &seed in &[0u32, 1, 2, ROOT_PID.0, u32::MAX - 1, u32::MAX] {
            let next = ProcessManager::get()
                .next_pid(seed)
                .expect("next_pid finds a free pid");
            assert!(
                !occupied(next),
                "next_pid({seed}) returned occupied pid {next}"
            );
        }

        let mut n = ROOT_PID.0;
        while occupied(n.wrapping_add(1)) {
            n = n.wrapping_add(1);
            if n == ROOT_PID.0 {
                // Table holds every allocatable pid — skip this assertion
                // rather than spin.
                break;
            }
        }
        if !occupied(n.wrapping_add(1)) {
            assert_eq!(
                ProcessManager::get().next_pid(n),
                Some(n.wrapping_add(1)),
                "next_pid stops at the first free candidate"
            );
        }
    }

    #[test]
    fn process_table_insert_get_remove() {
        let table = ProcessTable::new();

        let root = Process::new(ROOT_PID, Weak::new()).expect("Process::new failed");
        let child = Process::new(Pid(0), Arc::downgrade(&root)).expect("Process::new failed");
        let child_pid = child.pid();

        // Insert; the returned Arc is ptr-equal to the one stored.
        let stored_back = table.insert(Arc::clone(&child));
        assert!(Arc::ptr_eq(&stored_back, &child));

        // get returns a ptr-equal clone; the table retains its own ref so the
        // strong count is >= 2.
        let g = table
            .get(child_pid)
            .expect("get returned None after insert");
        assert!(Arc::ptr_eq(&g, &child));

        // get for a never-inserted pid is None.
        assert!(table.get(Pid(u32::MAX)).is_none());

        // remove drops the table's ref and returns the stored Arc (ptr-equal).
        let removed = table.remove(child_pid).expect("remove returned None");
        assert!(Arc::ptr_eq(&removed, &child));

        // After removal the pid is gone: both get and a second remove are None.
        assert!(table.get(child_pid).is_none());
        assert!(table.remove(child_pid).is_none());

        // Sanity: root is unaffected by being a weak parent here.
        assert_eq!(child.parent().map(|p| p.pid()), Some(ROOT_PID));
    }

    #[test]
    fn process_children_registered_on_create() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());
        assert_eq!(root.child_count(), 0);

        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let child_pid = child.pid();

        // The child is now visible under root's children map.
        assert_eq!(root.child_count(), 1);
        assert!(Arc::ptr_eq(
            &root.child(child_pid).expect("child lookup failed"),
            &child,
        ));
        // Unknown pid returns None.
        assert!(root.child(Pid(u32::MAX)).is_none());

        // Clean up so the global root is not polluted for later tests that
        // assert `root.has_no_children()` at entry.
        mgr.destroy_process(child_pid);
        assert!(root.has_no_children());
    }

    #[test]
    fn process_children_removed_on_destroy() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();

        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let child_pid = child.pid();
        assert_eq!(root.child_count(), 1);

        mgr.destroy_process(child_pid);
        assert!(root.child(child_pid).is_none());
        assert_eq!(root.child_count(), 0);
        assert!(root.has_no_children());
    }

    #[test]
    fn process_children_reparented_on_destroy() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());

        // mid is a child of root; grand is a child of mid.
        let mid = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let grand = mgr
            .create_process(Arc::downgrade(&mid))
            .expect("create_process failed");
        let grand_pid = grand.pid();
        assert_eq!(mid.child_count(), 1);
        assert_eq!(root.child_count(), 1); // mid

        drop(grand); // drop our strong ref; the table still holds grand
        mgr.destroy_process(mid.pid());

        // grand is still in the table, and its parent is now root.
        let grand_proc = mgr
            .process_table()
            .get(grand_pid)
            .expect("grandchild survived in table");
        assert!(Arc::ptr_eq(
            &grand_proc.parent().expect("grand has a parent"),
            &root
        ));
        // mid is gone from root's children; grand took its place.
        assert!(root.child(mid.pid()).is_none());
        assert!(root.child(grand_pid).is_some());
        assert_eq!(root.child_count(), 1);

        // Cleanup: leave root with no children for later tests.
        mgr.destroy_process(grand_pid);
        assert!(root.has_no_children());
    }

    #[test]
    fn process_root_has_no_parent() {
        let root = ProcessManager::get().root_process().clone();
        assert!(root.parent().is_none());
    }

    #[test]
    fn process_child_parent_roundtrip() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let parent = child.parent().expect("child has no parent");
        assert!(Arc::ptr_eq(&parent, &root));
        // Clean up so the global root is not polluted for later tests.
        mgr.destroy_process(child.pid());
        assert!(root.has_no_children());
    }

    #[test]
    fn process_for_each_child() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();

        let c1 = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let c2 = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");

        let mut visited: alloc::vec::Vec<Pid> = alloc::vec::Vec::new();
        root.for_each_child(|c| visited.push(c.pid()));
        visited.sort();

        let mut expected = alloc::vec![c1.pid(), c2.pid()];
        expected.sort();
        assert_eq!(visited, expected);

        // Clean up so the global root is not polluted for later tests that
        // assert `root.has_no_children()` at entry.
        mgr.destroy_process(c1.pid());
        mgr.destroy_process(c2.pid());
        assert!(root.has_no_children());
    }

    // Multi-threaded concurrency on root's parent/child topology
    #[test(thread = 3, repeat = 2)]
    fn process_concurrent_topology_mutation() {
        use core::sync::atomic::{AtomicUsize, Ordering};
        // Role allocator: 0 = adder, 1 = remover, 2 = reader.
        static ROLE: AtomicUsize = AtomicUsize::new(0);
        const ROLE_ADDER: usize = 0;
        const ROLE_REMOVER: usize = 1;
        const ROLE_READER: usize = 2;
        const ITERS: usize = 20;

        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        let role = ROLE.fetch_add(1, Ordering::Relaxed) % 3;

        match role {
            ROLE_ADDER => {
                // Create child processes under root
                let mut created: alloc::vec::Vec<Pid> = alloc::vec::Vec::new();
                for _ in 0..ITERS {
                    let child = mgr
                        .create_process(Arc::downgrade(&root))
                        .expect("create_process failed in adder");
                    created.push(child.pid());
                    crate::scheduler::yield_me();
                }
                // Cleanup: remove every pid we created
                for pid in created {
                    let _ = mgr.destroy_process(pid);
                }
            }
            ROLE_REMOVER => {
                // Destroy child processes that the adder created
                for _ in 0..ITERS {
                    // Collect at most one target pid under the read lock.
                    let target: Option<Pid> = {
                        let mut found: Option<Pid> = None;
                        root.for_each_child(|c| {
                            if found.is_none() {
                                found = Some(c.pid());
                            }
                        });
                        found
                    };
                    if let Some(pid) = target {
                        let _ = mgr.destroy_process(pid);
                    }
                    crate::scheduler::yield_me();
                }
            }
            _ => {
                // Reader: iterate `for_each_child` while adder/remover mutate
                // the same root's children map.
                let mut read_iters = 0usize;
                for _ in 0..ITERS {
                    let mut seen: alloc::vec::Vec<Pid> = alloc::vec::Vec::new();
                    root.for_each_child(|c| {
                        let parent = c.parent();
                        assert!(
                            parent.is_some(),
                            "for_each_child observed a child with no parent"
                        );
                        assert!(
                            Arc::ptr_eq(parent.as_ref().unwrap(), &root),
                            "for_each_child observed a child whose parent is not root"
                        );
                        seen.push(c.pid());
                    });
                    let mut sorted = seen.clone();
                    sorted.sort_unstable();
                    sorted.dedup();
                    assert_eq!(
                        seen.len(),
                        sorted.len(),
                        "for_each_child observed duplicate pids in one snapshot"
                    );
                    read_iters += 1;
                    crate::scheduler::yield_me();
                }
                assert!(read_iters > 0, "reader never iterated for_each_child");
            }
        }
    }

    // Exercise the `Alive -> Zombie -> Dead` lifecycle when `destroy_process`
    // is called while a process still owns a surviving thread.
    #[test]
    fn process_state_zombie_then_dead_on_last_thread() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());

        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let child_pid = child.pid();
        assert_eq!(child.state(), ProcessState::Alive);
        assert!(child.has_no_threads());

        // The worker waits on a 2-party barrier before retiring. This lets the
        // main thread request destroy before the worker retires, so the retire
        // path sees a `Zombie` process (not `Alive`) and routes through
        // `destroy_process`. `Builder::build` creates the worker without
        // enqueuing it for running, so `set_process` completes (in `add_thread`
        // below) before the worker can be scheduled — closing the race where
        // the worker retired with a dangling `process` `Weak`. Start it only
        // after linking.
        let release = Arc::new(crate::sync::ConstBarrier::<{ 2 }>::new());
        let release_w = release.clone();
        let worker =
            crate::thread::Builder::new(crate::thread::Entry::Closure(Box::new(move || {
                release_w.wait();
                crate::scheduler::retire_me();
            })))
            .build();

        // Link the worker to the child so the retire path can reach the child
        // through `old.process()`.
        assert!(child.add_thread(worker.clone()));
        let _ok = crate::scheduler::queue_ready_thread(crate::thread::IDLE, worker);
        assert_eq!(_ok, Ok(()));
        assert!(!child.has_no_threads());
        assert_eq!(child.state(), ProcessState::Alive);

        // Destroy requested while a thread survives: become `Zombie`, return
        // `None`. The child stays in the table and under root so the worker's
        // `Weak<Process>` keeps resolving.
        assert!(mgr.destroy_process(child_pid).is_none());
        assert_eq!(child.state(), ProcessState::Zombie);
        assert!(mgr.process_table().get(child_pid).is_some());
        assert!(root.child(child_pid).is_some());

        // A duplicate/racing destroy request is a no-op: still `Zombie`.
        assert!(mgr.destroy_process(child_pid).is_none());
        assert_eq!(child.state(), ProcessState::Zombie);

        // Release the worker. It retires; the retire path removes it from the
        // child's thread list, sees `has_no_threads()`, and calls
        // `destroy_process` — whose `Zombie` arm finalizes, completing the
        // deferred reclamation.
        release.wait();

        // Poll until the child reaches `Dead`. `become_dead()` is the last step
        // of `finalize_destroy`, so once state is `Dead` the pid has already
        // been removed from the table and from root's children. The retire path
        // runs asynchronously once the worker is dispatched to exit, so yield
        // between checks. The bound turns a hang into a loud failure. (Polling
        // `child()` or `process_table()` instead would race the ordering
        // between `remove_child`/`table.remove` and `become_dead`.)
        while child.state() != ProcessState::Dead {
            crate::scheduler::yield_me();
        }
        // Reaped: pid gone from the table, no longer a child of root, and the
        // process (still held alive by our local `child` Arc) is `Dead`.
        assert!(mgr.process_table().get(child_pid).is_none());
        assert!(root.child(child_pid).is_none());
        assert!(root.has_no_children());
    }

    #[test]
    fn process_state_destroy_races_last_thread_retire() {
        const ITERS: usize = 64;
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();

        for _ in 0..ITERS {
            let child = mgr
                .create_process(Arc::downgrade(&root))
                .expect("create_process failed");
            let child_pid = child.pid();
            assert_eq!(child.state(), ProcessState::Alive);

            // `Builder::build` creates the worker but does NOT enqueue it for
            // running (unlike `spawn`/`start`, which call `queue_ready_thread`
            // before returning). This closes the race where the worker could be
            // scheduled and retire before `add_thread`→`set_process` completes:
            // that left worker's `process` a dangling `Weak`, so the retire
            // path never reached `destroy_process` and the child stayed Zombie
            // forever (the original timeout root cause). Link first, then start.
            // No barrier: once started, the worker's retire races the main
            // thread's `destroy_process` below. Both interleavings converge on
            // Dead — this is the unique invariant test 2 verifies, distinct
            // from `process_state_zombie_then_dead_on_last_thread` which uses a
            // barrier to force the destroy-first ordering.
            let worker =
                crate::thread::Builder::new(crate::thread::Entry::Closure(Box::new(|| {
                    crate::scheduler::retire_me()
                })))
                .build();
            assert!(child.add_thread(worker.clone()));
            let _ok = crate::scheduler::queue_ready_thread(crate::thread::IDLE, worker);
            assert_eq!(_ok, Ok(()));

            // Race: the main thread requests destroy while the worker may
            // already be retiring (or retired) on another CPU. Regardless of
            // interleaving, the child must end up reaped: `destroy_process`
            // commits `Zombie` first, so exactly one of {destroy fast-path,
            // retire-path finalize} reclaims it.
            let _ = mgr.destroy_process(child_pid);

            // Poll until Dead: `become_dead` is the final step of
            // `finalize_destroy`, so Dead implies the pid is already gone from
            // the table and root's children.
            while child.state() != ProcessState::Dead {
                crate::scheduler::yield_me();
            }
            assert!(mgr.process_table().get(child_pid).is_none());
            assert!(root.child(child_pid).is_none());
        }
        assert!(root.has_no_children());
    }

    #[test]
    fn process_root_is_immortal() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert_eq!(root.pid(), ROOT_PID);
        assert_eq!(root.state(), ProcessState::Alive);

        // A direct destroy request on root is a no-op: state stays Alive, root
        // stays in the table, root_process() keeps resolving to the same Arc.
        assert!(mgr.destroy_process(ROOT_PID).is_none());
        assert_eq!(root.state(), ProcessState::Alive);
        assert!(mgr.process_table().get(ROOT_PID).is_some());
        assert!(Arc::ptr_eq(mgr.root_process(), &root));

        // A duplicate/racing destroy is still a no-op.
        assert!(mgr.destroy_process(ROOT_PID).is_none());
        assert_eq!(root.state(), ProcessState::Alive);
        assert!(Arc::ptr_eq(mgr.root_process(), &root));

        // The proof of immortality: root is still fully functional after the
        // (would-be) destroy. A child created under root resolves and reaps
        // cleanly, leaving root's topology pristine. If the guard had regressed
        // (root became Zombie/Dead), `create_process` under root would either
        // fail or leave the child's parent `Weak` dangling.
        let after = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process after root-destroy failed");
        assert_eq!(after.state(), ProcessState::Alive);
        assert_eq!(after.parent().map(|p| p.pid()), Some(ROOT_PID));
        // Threadless child: destroy finalizes straight through to Dead.
        assert!(mgr.destroy_process(after.pid()).is_some());
        assert_eq!(after.state(), ProcessState::Dead);
        assert!(mgr.process_table().get(after.pid()).is_none());
        assert!(root.child(after.pid()).is_none());
        assert!(root.has_no_children());
    }

    #[test]
    fn process_destroy_absent_and_dead_returns_none() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());

        // A pid that was never allocated. Pick one well clear of the live range
        // (the global counter is shared across tests, so assert absence rather
        // than a fixed value). `Pid(u32::MAX)` is reserved/never handed out by
        // `alloc_pid` (it short-circuits to `None` long before this).
        let absent = Pid(u32::MAX - 1);
        assert!(mgr.process_table().get(absent).is_none());
        assert!(mgr.destroy_process(absent).is_none());
        // No side effects: table and root topology unchanged.
        assert!(mgr.process_table().get(absent).is_none());
        assert!(root.has_no_children());

        // A process that is already `Dead`. Build one by destroying a
        // threadless child (Alive + no threads => `destroy_process` finalizes
        // straight through to Dead).
        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let child_pid = child.pid();
        assert_eq!(child.state(), ProcessState::Alive);
        assert!(child.has_no_threads());

        assert!(mgr.destroy_process(child_pid).is_some());
        assert_eq!(child.state(), ProcessState::Dead);
        assert!(mgr.process_table().get(child_pid).is_none());
        assert!(root.child(child_pid).is_none());

        // Now Dead: a second destroy is a no-op returning None. The process is
        // no longer in the table (so `table.get` already returns None), but if
        // it were still present this would still hit the `Dead => None` arm.
        assert!(mgr.destroy_process(child_pid).is_none());
        assert!(root.has_no_children());
    }

    #[test]
    fn process_add_thread_rejects_non_alive() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());

        // --- Zombie case -------------------------------------------------
        // To reach `Zombie` (not Dead) we need a surviving thread: destroy a
        // process that still owns a barrier-gated worker. The `Alive` arm of
        // `destroy_process` commits `Zombie` and, seeing threads remain,
        // returns `None` without finalizing.
        let zombie_child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let zombie_pid = zombie_child.pid();

        let release = Arc::new(crate::sync::ConstBarrier::<{ 2 }>::new());
        let release_w = release.clone();
        let keeper = crate::thread::spawn(move || {
            release_w.wait();
            crate::scheduler::retire_me();
        })
        .expect("spawn keeper failed");
        assert!(zombie_child.add_thread(keeper));
        assert!(mgr.destroy_process(zombie_pid).is_none());
        assert_eq!(zombie_child.state(), ProcessState::Zombie);

        // A thread built but not yet linked. `add_thread` to a `Zombie`
        // process must return `false` and must leave the thread's `process`
        // `Weak` empty (never set by `set_process`).
        let mut reject =
            crate::thread::Builder::new(crate::thread::Entry::C(never_run_entry)).build();
        assert!(!zombie_child.add_thread(reject.clone()));
        assert!(reject.process().is_none());

        // Detach the rejected thread from the global queue so it doesn't leak;
        // the Arc then drops to zero and the Thread is reclaimed. `Drop for
        // Thread` debug-asserts both `sched_node` and `process_node` are
        // detached — satisfied here (sched via this remove, process_node was
        // never linked since `add_thread` returned false).
        assert!(crate::thread::GlobalQueueVisitor::remove(&mut reject));

        // Release the keeper so the Zombie child finalizes and reaps.
        release.wait();
        let mut spins = 0u32;
        while root.child(zombie_pid).is_some() {
            crate::scheduler::yield_me();
            spins += 1;
            assert!(spins < 100_000, "zombie child never reaped");
        }
        assert_eq!(zombie_child.state(), ProcessState::Dead);

        // --- Dead case ---------------------------------------------------
        // A Dead process is even lower-leverage: `add_thread` must reject it
        // too. Build a Dead child (threadless destroy finalizes to Dead).
        let dead_child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let dead_pid = dead_child.pid();
        assert!(mgr.destroy_process(dead_pid).is_some());
        assert_eq!(dead_child.state(), ProcessState::Dead);

        let mut reject2 =
            crate::thread::Builder::new(crate::thread::Entry::C(never_run_entry)).build();
        assert!(!dead_child.add_thread(reject2.clone()));
        assert!(reject2.process().is_none());
        assert!(crate::thread::GlobalQueueVisitor::remove(&mut reject2));

        assert!(root.has_no_children());
    }

    #[test]
    fn process_remove_thread_semantics() {
        let mgr = ProcessManager::get();
        let root = mgr.root_process().clone();
        assert!(root.has_no_children());

        let child = mgr
            .create_process(Arc::downgrade(&root))
            .expect("create_process failed");
        let child_pid = child.pid();

        // --- False path: thread not linked to this process ----------------
        // Build a thread but never `add_thread` it. Its `process_node` is not
        // linked to any process list, so `ThreadList::detach` returns `false`
        // and `remove_thread` propagates that without touching `set_process`.
        let mut unlinked =
            crate::thread::Builder::new(crate::thread::Entry::C(never_run_entry)).build();
        assert!(unlinked.process().is_none());
        assert!(!child.remove_thread(&mut unlinked));
        // Still no owner, and the child's thread list is still empty.
        assert!(unlinked.process().is_none());
        assert!(child.has_no_threads());
        // Detach from the global queue so the unlinked thread doesn't leak.
        assert!(crate::thread::GlobalQueueVisitor::remove(&mut unlinked));

        // --- Success path: linked then removed ----------------------------
        // A barrier-gated worker so we control when it retires. `add_thread`
        // links it and sets `process` to the child's `Weak`; `remove_thread`
        // detaches and clears the `Weak` back to empty.
        let release = Arc::new(crate::sync::ConstBarrier::<{ 2 }>::new());
        let release_w = release.clone();
        let worker = crate::thread::spawn(move || {
            release_w.wait();
            crate::scheduler::retire_me();
        })
        .expect("spawn worker failed");
        assert!(child.add_thread(worker.clone()));
        assert!(!child.has_no_threads());
        assert_eq!(worker.process().map(|p| p.pid()), Some(child_pid));

        // Remove the worker from the child's list *before* it retires. After a
        // successful remove, the worker's `process()` is `None` again.
        let mut worker_mut = worker.clone();
        assert!(child.remove_thread(&mut worker_mut));
        assert!(worker.process().is_none());
        assert!(child.has_no_threads());

        // Reap the child ourselves. We just cleared the worker's `process`
        // `Weak`, so when the worker retires its retire path will see
        // `old.process() == None` and *not* call `destroy_process` for the
        // child — left to its own, the child would leak as a threadless
        // `Alive` process. Destroying it now (threadless => straight to Dead)
        // reclaims it deterministically. The worker, still scheduled, later
        // retires harmlessly: its `process()` is `None`, so it touches no
        // process; `take_cleanup` (None for a `spawn` closure) reaps it.
        assert!(mgr.destroy_process(child_pid).is_some());
        assert_eq!(child.state(), ProcessState::Dead);
        assert!(root.child(child_pid).is_none());

        // Release the barrier so the detached worker actually runs and
        // retires. The worker's `process()` is `None`, so its retire path
        // touches no process; it just transitions to `RETIRED` and the
        // scheduler reaps the worker Arc itself once it switches out. Poll for
        // the `RETIRED` state so a hang (e.g. worker never scheduled) becomes a
        // loud failure rather than a silent leak into the next test.
        release.wait();
        let mut spins = 0u32;
        while worker.state() != crate::thread::RETIRED {
            crate::scheduler::yield_me();
            spins += 1;
            assert!(spins < 100_000, "detached worker never retired");
        }
        assert!(root.has_no_children());
    }
}
