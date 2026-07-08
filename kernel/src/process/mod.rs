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

//! Process abstraction for AArch64.
//!
//! A Process represents a user-space execution context with its own
//! address space (page table).  Processes are not scheduling entities;
//! Thread is the only schedulable unit.  The Process lifetime is managed
//! by `Arc<Process>` reference counting — there is no state machine
//! (see [[process-no-state-machine]]).
//!
//! Each Thread holds a non-owning raw pointer back to its Process
//! (`Option<NonNull<Process>>`).  When the last `Arc<Process>` is
//! dropped, the address space (page table) is freed and all threads
//! referencing this process observe a null process pointer.

pub mod elf;
#[cfg(target_arch = "aarch64")]
pub(crate) mod first_process;
pub(crate) mod loader;
#[cfg(target_arch = "aarch64")]
pub(crate) mod vm;

use crate::{
    arch::aarch64::mmu::{self, PageTableManager},
    mm::{kernel_phys_to_virt, kernel_virt_to_phys},
    types::Arc,
};
use alloc::vec::Vec;
use core::{
    alloc::Layout,
    ptr::NonNull,
    sync::atomic::{fence, AtomicBool, AtomicI32, AtomicU32, AtomicU64, AtomicU8, Ordering},
};

// Global storage for the first user-space process (AArch64 Phase 3).
// Keeps the Process alive after init_first_process returns.
#[cfg(target_arch = "aarch64")]
pub(crate) static FIRST_PROCESS: crate::sync::SpinLock<Option<Arc<Process>>> =
    crate::sync::SpinLock::new(None);

// ---------------------------------------------------------------------------
// PID allocator (task 3.2)
// ---------------------------------------------------------------------------

static NEXT_PID: AtomicU32 = AtomicU32::new(1);

fn alloc_pid() -> u32 {
    NEXT_PID.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// ASID allocator (Phase 5a — generation-aware, see design D1)
// ---------------------------------------------------------------------------
// 8-bit ASID space: values 1..=255. Value 0 is reserved (kernel / no process).
//
// A generation counter per slot makes recycling safe: when an ASID is assigned
// to a new process, its generation is bumped and `TLBI ASIDE1IS` is broadcast
// for that ASID, invalidating any stale TLB entries tagged with the old
// (asid, generation) pair.  See `asid-generation` spec and design D1.
//
// Soundness invariant (the bug the review caught): the bump + `ASIDE1IS`
// happens on **every** `alloc` — free-slot path included — not only on LRU
// recycle.  Skipping it on the free-slot path would return the same
// (asid, gen) pair as a dead process and leave that process's stale TLB
// entries valid for the new owner.

/// Number of ASID slots.  Slot 0 is reserved (kernel / untagged); user
/// processes use slots `1..=255`.
const ASID_SLOTS: usize = 256;

/// Initial value of every `generations` slot.  `u8::MAX` so that the first
/// `alloc` of a slot bumps to `0`, matching the `asid-generation` spec
/// scenario "First process gets ASID 1 generation 0".
const ASID_GEN_INIT: u8 = u8::MAX;

/// A generation-aware ASID allocator.
///
/// Constructible (via [`AsidAllocator::new`]) so tests can instantiate a
/// fresh allocator and get deterministic results independent of test
/// ordering.  Production uses a single const-init `static`
/// ([`ASID_ALLOCATOR`]).
pub(crate) struct AsidAllocator {
    /// Current generation per ASID slot.  Bumped on every assignment of the
    /// slot to a new process.  Starts at `u8::MAX` so the first assignment
    /// yields generation `0`.
    generations: [AtomicU8; ASID_SLOTS],
    /// Monotonic "tick" stamped on each `alloc`, used to pick the LRU victim
    /// when all slots are live.  Smallest `last_used` == coldest.
    last_used: [AtomicU64; ASID_SLOTS],
    /// Slot-occupied bitmap.  `true` while a live process holds the slot.
    /// Cleared by `free` (called from `Process::drop`).
    live: [AtomicBool; ASID_SLOTS],
    /// Counter incremented on every `alloc`, used to stamp `last_used`.
    next_tick: AtomicU64,
}

impl AsidAllocator {
    /// A const-constructible empty allocator (all slots free, all generations
    /// at `u8::MAX`).  Used to initialise the production `static`.
    pub(crate) const EMPTY: Self = Self {
        generations: [const { AtomicU8::new(ASID_GEN_INIT) }; ASID_SLOTS],
        last_used: [const { AtomicU64::new(0) }; ASID_SLOTS],
        live: [const { AtomicBool::new(false) }; ASID_SLOTS],
        next_tick: AtomicU64::new(0),
    };

    /// Construct a fresh allocator (for tests).
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::EMPTY
    }

    /// Allocate an ASID for a new process.
    ///
    /// Returns `(asid, generation)` where `asid ∈ 1..=255`.  Never panics: if
    /// all 255 user slots are live, the least-recently-used slot is recycled.
    ///
    /// On every call — free-slot or recycled — this bumps the slot's
    /// generation and broadcasts `TLBI ASIDE1IS, <asid>` (Inner Shareable)
    /// followed by DSB + ISB.  That broadcast is what makes the generation
    /// mechanism sound: any stale TLB entries tagged with the slot's previous
    /// generation are invalidated before the new process can use the ASID.
    pub(crate) fn alloc(&self) -> (u8, u8) {
        // 1. Pick a slot: first free (linear scan), else LRU victim.
        let slot = self.pick_slot();

        // 2. Bump generation (wrapping u8).  Because generations start at
        //    u8::MAX, the first bump of a slot yields 0.
        //    Release so a concurrent `free()` on another CPU that Acquire-loads
        //    the generation observes the bump before clearing `live`.
        let new_gen = self.generations[slot]
            .fetch_add(1, Ordering::Release)
            .wrapping_add(1);

        // 3. Invalidate stale TLB entries for this ASID, then synchronise.
        //    Inner-Shareable so other CPUs observe the invalidation.
        let asid = slot as u8;
        crate::arch::aarch64::asm::tlbi_aside1is(asid);
        crate::arch::aarch64::asm::dsb(crate::arch::aarch64::asm::DsbOptions::InnerShareable);
        crate::arch::aarch64::asm::isb();

        // 4. Stamp + mark live.  Release on `live` so `pick_slot` on another
        //    CPU which Acquire-loads `live` sees the new generation first.
        let tick = self.next_tick.fetch_add(1, Ordering::Relaxed);
        self.last_used[slot].store(tick, Ordering::Relaxed);
        self.live[slot].store(true, Ordering::Release);

        (asid, new_gen)
    }

    /// Release an ASID slot when its process is dropped.
    ///
    /// Clears `live[asid]` only if `generations[asid]` still equals the
    /// recorded `generation` — a generation guard.  This prevents a stale
    /// `Drop` (for a process whose slot was already recycled to a new owner)
    /// from clearing `live` on the new owner's slot.
    ///
    /// Does **not** bump the generation or invalidate: that is `alloc`'s job
    /// when the slot is next assigned.  So `free` is cheap (no broadcast).
    pub(crate) fn free(&self, asid: u8, generation: u8) {
        let slot = asid as usize;
        if slot == 0 {
            return;
        }
        // Only clear if the generation still matches ours.  If the slot was
        // recycled since we recorded (asid, generation), generations[slot]
        // will differ and we leave the new owner's `live` flag alone.
        //
        // Acquire on the generation load to pair with alloc's Release on the
        // bump; Release on the `live` store so a subsequent `pick_slot` on
        // another CPU sees the cleared flag.
        if self.generations[slot].load(Ordering::Acquire) == generation {
            self.live[slot].store(false, Ordering::Release);
        }
    }

    /// Pick a slot to assign: the first free slot (linear scan), or, if all
    /// are live, the LRU victim (smallest `last_used`).
    fn pick_slot(&self) -> usize {
        // Fast path: first free slot in 1..=255 (slot 0 reserved).
        // Acquire to pair with `free`'s Release store of `false`.
        for n in 1..ASID_SLOTS {
            if !self.live[n].load(Ordering::Acquire) {
                return n;
            }
        }
        // Slow path: all live — recycle the LRU victim.  Slot 0 is reserved,
        // so start the search at 1.
        let mut victim = 1usize;
        let mut min_tick = self.last_used[1].load(Ordering::Relaxed);
        for n in 2..ASID_SLOTS {
            let t = self.last_used[n].load(Ordering::Relaxed);
            if t < min_tick {
                min_tick = t;
                victim = n;
            }
        }
        victim
    }
}

/// The production ASID allocator.  Const-initialised (all slots free).
// SAFETY: `AsidAllocator` contains only atomic integers; it is `Sync` by
// construction (all access is via atomic operations).
static ASID_ALLOCATOR: AsidAllocator = AsidAllocator::EMPTY;

// ---------------------------------------------------------------------------
// AddressSpace
// ---------------------------------------------------------------------------

/// A process-specific address space, rooted at a L1 page table.
///
/// The `root` is a pointer to the L1 `PageTableManager` that will be
/// installed in TTBR0_EL1 when this process is scheduled.  It is
/// allocated and zeroed on construction and freed (along with all
/// lower-level tables) on drop.
///
/// During Phase 2 the address space is initially empty (no user
/// mappings).  Virtual memory region tracking will be added in a
/// later phase.
pub struct AddressSpace {
    /// Pointer to the L1 page table (root of the translation table walk).
    root: NonNull<PageTableManager>,
    /// Kernel heap allocations backing user-space mappings (ELF segments, stack).
    /// Freed in Drop after the page table tree is released.
    allocs: Vec<(*mut u8, Layout)>,
}

// SAFETY: `AddressSpace` owns the page table exclusively (single-threaded
// access while not scheduled).  `Send` + `Sync` are safe because the owning
// `Process` is protected by `Arc` and the page table is only accessed when
// the process's threads are not concurrently running.
unsafe impl Send for AddressSpace {}
unsafe impl Sync for AddressSpace {}

impl AddressSpace {
    /// Allocate and initialise a new (empty) address space.
    ///
    /// # Errors
    /// Returns `&'static str` if the page-table allocation fails.
    pub fn try_new() -> Result<Self, &'static str> {
        let raw = mmu::alloc_page_table()?;
        Ok(Self {
            root: unsafe { NonNull::new_unchecked(raw) },
            allocs: Vec::new(),
        })
    }

    /// Register a kernel heap allocation that backs a user-space mapping.
    ///
    /// The allocation is freed in `AddressSpace::drop` after the page table
    /// tree has been released.
    pub(crate) fn track_alloc(&mut self, ptr: *mut u8, layout: Layout) {
        self.allocs.push((ptr, layout));
    }

    /// Return the physical address of the root page table.
    ///
    /// Write this value directly to TTBR0_EL1 via `.set(pa as u64)`.
    /// The hardware extracts BADDR from bits [47:1] internally.
    #[inline]
    pub fn root_pa(&self) -> usize {
        let va = self.root.as_ptr() as usize;
        kernel_virt_to_phys(va)
    }

    /// Return a raw pointer to the root page table (virtual address).
    #[inline]
    pub fn root_ptr(&self) -> *mut PageTableManager {
        self.root.as_ptr()
    }
}

impl Drop for AddressSpace {
    fn drop(&mut self) {
        // Recursively free the entire page-table tree.
        // SAFETY: `root` was allocated by `alloc_page_table()` and is
        // not shared — we are the sole owner.
        unsafe {
            mmu::free_page_table(self.root.as_ptr());
        }
        // Free kernel heap allocations that backed user-space mappings.
        // The page table is gone so these pages are no longer reachable from
        // user space; we can safely return them to the allocator.
        for (ptr, layout) in self.allocs.drain(..) {
            unsafe { alloc::alloc::dealloc(ptr, layout) };
        }
    }
}

// ---------------------------------------------------------------------------
// Process
// ---------------------------------------------------------------------------

/// A user-space process.
///
/// Each process has a unique address space and owns zero or more threads.
/// Process lifetime is managed by `Arc<Process>` reference counting.
/// There is no zombie / exited state — when the last reference is dropped
/// the page table is freed automatically.
///
/// # Thread-to-Process back-reference
///
/// Threads hold a non-owning `Option<NonNull<Process>>` pointing to their
/// owning process.  This pointer becomes dangling once the `Process` is
/// dropped, so threads must check `process()` before dereferencing.
/// Because `Process` owns `Arc<Thread>` references, a thread can be
/// confident its process is alive as long as it holds its own `ThreadNode`.
pub struct Process {
    /// The address space (page table root) for this process.
    pub address_space: AddressSpace,
    /// Process ID allocated by `alloc_pid()`.  PID 1 is the init process.
    pub pid: u32,
    /// AArch64 ASID (8-bit, 1..=255).  Encoded in TTBR0_EL1[55:48] so the
    /// MMU can scope TLB entries per process, enabling `TLBI ASIDE1IS`.
    pub asid: u8,
    /// Generation of the ASID slot when it was assigned to this process.
    /// Together with `asid` this forms the `(asid, generation)` pair the
    /// scheduler validates on PA-cache hits (design D4) and the allocator
    /// checks in `free` (design D1).
    pub asid_generation: u8,
    /// Process exit code.  `i32::MIN` is the "not exited" sentinel: it is
    /// outside the POSIX exit-status range (`0..=255`), so any real exit
    /// code (including `0`) is distinguishable from "not exited".  Read by a
    /// future `waitpid` (Phase 5c) on a different thread/CPU than the one
    /// that called `exit`, hence `Release`/`Acquire` ordering.
    pub exit_code: AtomicI32,
    /// Threads belonging to this process.
    threads: Vec<crate::thread::ThreadNode>,
}

/// Sentinel value for `Process::exit_code` meaning "this process has not
/// exited yet".  `i32::MIN` is outside the POSIX `0..=255` exit-status range.
const EXIT_NOT_EXITED: i32 = i32::MIN;

impl Process {
    /// Create a new process with an empty address space.
    ///
    /// # Errors
    /// Returns the `&'static str` error from `AddressSpace::try_new()`
    /// if the page-table allocation fails.
    pub fn try_new() -> Result<Arc<Self>, &'static str> {
        let address_space = AddressSpace::try_new()?;
        let (asid, asid_generation) = ASID_ALLOCATOR.alloc();
        Ok(Arc::new(Self {
            address_space,
            pid: alloc_pid(),
            asid,
            asid_generation,
            exit_code: AtomicI32::new(EXIT_NOT_EXITED),
            threads: Vec::new(),
        }))
    }

    /// Record this process's exit code.
    ///
    /// `Release` ordering so a subsequent `Acquire` load (e.g. `waitpid` on
    /// another CPU in Phase 5c) observes the stored code.
    #[inline]
    pub fn set_exit_code(&self, code: i32) {
        self.exit_code.store(code, Ordering::Release);
    }

    /// Read this process's exit code.  Returns [`EXIT_NOT_EXITED`] (`i32::MIN`)
    /// if the process has not exited.
    ///
    /// `Acquire` ordering to pair with [`set_exit_code`]'s `Release`.
    #[inline]
    pub fn exit_code(&self) -> i32 {
        self.exit_code.load(Ordering::Acquire)
    }

    /// Register a thread as belonging to a process.
    ///
    /// This pushes the thread into the process's thread list and sets
    /// the thread's back-pointer (see [`crate::thread::Thread::set_process`]).
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` has more than one reference (i.e., the process
    /// has already been shared).
    pub(crate) fn attach_thread(process: &mut Arc<Process>, thread: &crate::thread::ThreadNode) {
        // SAFETY: We hold a unique `Arc<Process>`, so the pointer is alive
        // for the duration of this call.  The raw pointer stored in the
        // thread is valid until the Process is dropped.
        let this = unsafe { NonNull::new_unchecked(Arc::as_ptr(process) as *mut Process) };
        let proc = Arc::get_mut(process).expect("attach_thread: Arc must have unique ownership");
        thread.set_process(this);
        proc.threads.push(thread.clone());
    }

    /// Iterate over the threads attached to this process.
    pub fn threads(&self) -> &[crate::thread::ThreadNode] {
        &self.threads
    }
}

// `Arc<Process>` is sent between cores when the scheduler migrates threads.
unsafe impl Send for Process {}
unsafe impl Sync for Process {}

impl Drop for Process {
    fn drop(&mut self) {
        // Release this process's ASID slot back to the allocator.  The
        // generation guard inside `free` ensures a stale `Drop` (slot already
        // recycled to a new owner) is a no-op rather than corrupting the new
        // owner's `live` flag.  `free` does not broadcast — the next `alloc`
        // of this slot does the bump + `ASIDE1IS`.
        ASID_ALLOCATOR.free(self.asid, self.asid_generation);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_alloc_pid_increases() {
        let a = alloc_pid();
        let b = alloc_pid();
        let c = alloc_pid();
        assert!(b > a, "PIDs must be monotonically increasing");
        assert!(c > b, "PIDs must be monotonically increasing");
    }

    // ---- ASID allocator unit tests (Phase 5a §5) ----
    // These construct a *fresh* `AsidAllocator` so results are deterministic
    // and independent of test ordering or the production `ASID_ALLOCATOR`.

    // 5.2: First alloc on a fresh allocator returns ASID 1, generation 0.
    // (generations start at u8::MAX, so the first bump wraps to 0.)
    #[test]
    fn test_alloc_asid_first_is_one() {
        let a = AsidAllocator::new();
        let (asid, gen) = a.alloc();
        assert_eq!(asid, 1, "first alloc must return ASID 1 (slot 0 reserved)");
        assert_eq!(gen, 0, "first alloc must return generation 0");
    }

    // 5.1: Successive allocs return distinct (asid, gen) pairs while slots
    // remain free.  Each fresh slot gets generation 0 (its first bump); the
    // asids differ because they come from different slots.
    #[test]
    fn test_alloc_asid_unique() {
        let a = AsidAllocator::new();
        let (a1, g1) = a.alloc();
        let (a2, g2) = a.alloc();
        assert_ne!(a1, a2, "distinct slots must have distinct ASIDs");
        assert_eq!(g1, 0, "fresh slot's first generation is 0");
        assert_eq!(g2, 0, "fresh slot's first generation is 0");
    }

    // 5.1 companion: ASIDs advance through the free slots 1, 2, 3, ...
    #[test]
    fn test_alloc_asid_increases() {
        let a = AsidAllocator::new();
        let (a1, _) = a.alloc();
        let (a2, _) = a.alloc();
        let (a3, _) = a.alloc();
        assert_eq!(a1, 1);
        assert_eq!(a2, 2);
        assert_eq!(a3, 3);
    }

    // 5.3: 256 allocations on a fresh allocator (no frees) fill all 255 user
    // slots and force one LRU recycle.  Must not panic, and the recycled
    // slot's generation must be strictly greater than its first value (0).
    #[test]
    fn test_asid_recycle_does_not_panic() {
        let a = AsidAllocator::new();
        let (first_asid, first_gen) = a.alloc(); // slot 1, gen 0, tick 0
        assert_eq!(first_asid, 1);
        assert_eq!(first_gen, 0);
        // Fill the remaining 254 free slots (2..=255): allocs 2..=255.
        for _ in 0..254 {
            let (_asid, _gen) = a.alloc(); // must not panic
        }
        // The 256th alloc finds all 255 user slots live and recycles the LRU
        // victim — slot 1 (tick 0, the smallest).  Its generation is now 1.
        let (recycled_asid, recycled_gen) = a.alloc();
        assert_eq!(
            recycled_asid, first_asid,
            "LRU victim should be the oldest slot (ASID 1)"
        );
        assert!(
            recycled_gen > first_gen,
            "recycled slot's generation ({}) must exceed its previous value ({})",
            recycled_gen,
            first_gen
        );
    }

    // 5.4 — CRITICAL soundness regression test for the review's finding.
    // Reusing a freshly-freed slot MUST bump the generation (so the dead
    // process's stale TLB entries, tagged with the old generation, are not
    // valid for the new owner).  The original "fast path skips TLBI" design
    // returned the same (asid, gen) pair — this test fails on that design.
    #[test]
    fn test_reuse_free_slot_bumps_generation() {
        let a = AsidAllocator::new();
        let (asid, gen1) = a.alloc();
        a.free(asid, gen1);
        let (asid2, gen2) = a.alloc();
        assert_eq!(asid2, asid, "freed slot should be reused first");
        assert_ne!(
            gen2, gen1,
            "reuse MUST bump generation so stale TLB entries are invalidated"
        );
    }

    // 5.5: free() makes a slot reusable (the live bitmap is cleared).
    #[test]
    fn test_free_makes_slot_reusable() {
        let a = AsidAllocator::new();
        let (asid, gen) = a.alloc();
        a.free(asid, gen);
        // Next alloc should reuse the freed slot (ASID 1) rather than
        // advancing to ASID 2.
        let (asid2, _gen2) = a.alloc();
        assert_eq!(asid2, asid, "freed slot must be reusable");
    }

    // 5.6: free() with a stale generation is a no-op — it must NOT clear
    // `live` for a slot that was since recycled to a new owner.
    #[test]
    fn test_free_with_stale_generation_is_noop() {
        let a = AsidAllocator::new();
        let (asid, gen1) = a.alloc();
        a.free(asid, gen1);
        // Reassign the slot: alloc bumps the generation to gen2.
        let (_asid2, gen2) = a.alloc();
        assert_eq!(asid, _asid2, "same slot reused");
        assert_ne!(gen2, gen1, "generation bumped on reassign");
        // Now free with the STALE generation.  This must NOT clear live[asid]
        // (the slot's current generation is gen2, not gen1).
        a.free(asid, gen1);
        // The next alloc should NOT reuse this slot (it's still live under
        // gen2); it must advance to the next free slot (ASID 2).
        let (asid3, _gen3) = a.alloc();
        assert_ne!(
            asid3, asid,
            "stale-generation free must not free the live slot"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_process_asid_nonzero() {
        let p = Process::try_new().expect("Process::try_new failed");
        assert!(
            p.asid > 0,
            "ASID 0 is reserved for kernel; process ASIDs start at 1"
        );
        // 6.5: the generation of the assigned ASID is recorded on the process.
        // We don't assert a specific value: Process::try_new uses the global
        // ASID_ALLOCATOR, whose slots may have been bumped by earlier tests
        // or by init_first_process.  The generation just needs to be present
        // and consistent with what was allocated (validated implicitly by the
        // scheduler's 3-key cache check at context-switch time).
        let _ = p.asid_generation;
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_process_pid_nonzero() {
        let p = Process::try_new().expect("Process::try_new failed");
        assert!(p.pid > 0, "PID 0 is reserved; allocated PIDs start at 1");
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_two_processes_have_distinct_pids() {
        let p1 = Process::try_new().expect("Process::try_new failed");
        let p2 = Process::try_new().expect("Process::try_new failed");
        assert_ne!(
            p1.pid, p2.pid,
            "each Process::try_new must yield a unique PID"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_two_processes_have_distinct_asids() {
        let p1 = Process::try_new().expect("Process::try_new failed");
        let p2 = Process::try_new().expect("Process::try_new failed");
        assert_ne!(
            p1.asid, p2.asid,
            "each Process::try_new must yield a unique ASID"
        );
        // 6.5: two live processes must have distinct (asid, generation) pairs.
        // Distinct ASIDs already guarantee this, but assert the pair (not just
        // the asid) so the generation field's participation in the identity
        // is documented and would catch a future bug that nullified it.
        assert_ne!(
            (p1.asid, p1.asid_generation),
            (p2.asid, p2.asid_generation),
            "two live processes must have distinct (asid, generation) pairs"
        );
    }

    // ---- Process exit_code tests (Phase 5a §6) ----

    // 6.1: A fresh process reports the not-exited sentinel (i32::MIN),
    // distinguishing it from any real exit code including 0.  Matches the
    // process-management spec scenario "New process starts in the not-exited
    // state".
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_new_process_not_exited_sentinel() {
        let p = Process::try_new().expect("Process::try_new failed");
        assert_eq!(
            p.exit_code(),
            i32::MIN,
            "fresh process must report the not-exited sentinel (i32::MIN)"
        );
    }

    // 6.2: set_exit_code(0) then read 0 — this is the regression the sentinel
    // exists to catch: a real exit(0) must be distinguishable from "not
    // exited".
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_set_exit_code_roundtrip() {
        let p = Process::try_new().expect("Process::try_new failed");
        assert_ne!(p.exit_code(), 0, "sentinel must differ from a real exit(0)");
        p.set_exit_code(0);
        assert_eq!(
            p.exit_code(),
            0,
            "exit(0) must read back as 0, not the sentinel"
        );
    }

    // 6.3: a positive exit code round-trips.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_set_exit_code_positive() {
        let p = Process::try_new().expect("Process::try_new failed");
        p.set_exit_code(42);
        assert_eq!(
            p.exit_code(),
            42,
            "exit_code must round-trip a positive value"
        );
    }
}
