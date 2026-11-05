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

extern crate alloc;

use crate::{
    error,
    sync::{Mutex, MutexGuard},
    types::Arc,
};
use alloc::collections::BTreeMap;
use core::cell::UnsafeCell;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MmapFlags(u8);

impl MmapFlags {
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXECUTE: Self = Self(1 << 2);

    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn contains(self, requested: Self) -> bool {
        self.0 & requested.0 == requested.0
    }

    pub const fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitOr for MmapFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

/// A contiguous virtual-address range `[start, end)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Vma {
    start: usize,
    end: usize,
    flags: MmapFlags,
}

impl Vma {
    /// Returns [`error::code::EINVAL`] if the range is empty or inverted
    /// (`start >= end`).
    pub const fn new(start: usize, end: usize, flags: MmapFlags) -> Result<Self, error::Error> {
        if start >= end {
            return Err(error::code::EINVAL);
        }
        Ok(Self { start, end, flags })
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }

    pub fn flags(&self) -> MmapFlags {
        self.flags
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.end == self.start
    }

    /// `true` when `addr` lies in `[start, end)`.
    pub fn contains(&self, addr: usize) -> bool {
        self.start <= addr && addr < self.end
    }

    pub(crate) fn set_end(&mut self, new_end: usize) -> Result<(), error::Error> {
        if new_end <= self.start {
            return Err(error::code::EINVAL);
        }
        self.end = new_end;
        Ok(())
    }

    /// Change `start`. Because `start` is the BTreeMap key, the caller **must**
    /// remove the node from the tree and re-insert it under the new key after
    /// this call (see the [`AddressSpace`] invariant). Re-validates
    /// `start < end`.
    pub(crate) fn set_start(&mut self, new_start: usize) -> Result<(), error::Error> {
        if new_start >= self.end {
            return Err(error::code::EINVAL);
        }
        self.start = new_start;
        Ok(())
    }

    pub(crate) fn set_flags(&mut self, flags: MmapFlags) {
        self.flags = flags;
    }
}

/// Debug-only guard for the [`AddressSpace`] re-entrancy
macro_rules! assert_not_reentrant {
    ($aspace:expr) => {
        debug_assert!(
            !$aspace.lock.is_recursively_held(),
            "re-entrant AddressSpace access (nesting_count > 1) \
             — a method was called while the tree mutex was already held \
             by this thread (e.g. from within a for_each closure)"
        );
    };
}

/// A process's independent virtual address space.
pub struct AddressSpace {
    lock: Arc<Mutex>,
    vmas: UnsafeCell<BTreeMap<usize, Vma>>,
}

// SAFETY: `vmas` is an `UnsafeCell`, so `AddressSpace` gets no auto `Send` or
// `Sync`. Both are safe to promise by hand: all access to `vmas` funnels
// through `Self::lock` (`lock.lock_guard(&self.vmas)`), and the returned
// `MutexGuard` hands out `&mut BTreeMap` only while the mutex is held. The
// `BTreeMap` never escapes the guard (methods return `Vma` snapshots), so no
// unsynchronized access can exist.
//
// Note the lock itself: `Mutex` is already `Sync` (its state is
// atomic/spin-guarded) and is deliberately `!Send` because the PI chain's
// waitqueue bookkeeping assumes the mutex stays put — that is satisfied here
// since the `Arc<Mutex>` pins it. `Send` for `AddressSpace` requires moving
// the `Arc<Mutex>` handle (cheap, sound) — never the `Mutex` out of its
// allocation.
unsafe impl Send for AddressSpace {}
unsafe impl Sync for AddressSpace {}

impl AddressSpace {
    pub fn new() -> Self {
        Self {
            lock: Mutex::create(),
            vmas: UnsafeCell::new(BTreeMap::new()),
        }
    }

    /// Insert `vma` into this address space.
    ///
    /// Returns [`EEXIST`] if the new range overlaps an existing
    /// VMA. On failure the space is left unchanged.
    pub fn insert(&self, vma: Vma) -> Result<(), error::Error> {
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        let (start, end) = (vma.start(), vma.end());
        if Self::overlaps(&vmas, start, end) {
            Err(error::code::EEXIST)
        } else {
            vmas.insert(start, vma);
            Ok(())
        }
    }

    /// Reserve a `[start, end)` VA range with `flags` at the caller-chosen
    /// address. Returns a snapshot of the inserted [`Vma`].
    /// # Errors
    /// - [`EINVAL`] — `start >= end` (empty/inverted range).
    /// - [`EEXIST`] — the range overlaps an existing VMA.
    pub fn reserve(&self, start: usize, end: usize, flags: MmapFlags) -> Result<Vma, error::Error> {
        let vma = Vma::new(start, end, flags)?;
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        if Self::overlaps(&vmas, start, end) {
            Err(error::code::EEXIST)
        } else {
            vmas.insert(start, vma);
            Ok(vma)
        }
    }

    /// Remove and return a snapshot of the VMA whose start address equals
    /// `start`, if any.
    pub fn remove(&self, start: usize) -> Option<Vma> {
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        vmas.remove(&start)
    }

    /// Grow the VMA at `start` so its `end` becomes `new_end` (`> start`).
    ///
    /// # Errors
    /// - [`ENOENT`] — no VMA at `start`.
    /// - [`EINVAL`] — `new_end <= start`, or the grown range
    ///   would overlap the next VMA.
    pub fn extend_up(&self, start: usize, new_end: usize) -> Result<(), error::Error> {
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        if let Some((next_start, _)) = vmas.range(start + 1..).next() {
            if *next_start < new_end {
                return Err(error::code::EINVAL);
            }
        }
        let vma = vmas.get_mut(&start).ok_or(error::code::ENOENT)?;
        vma.set_end(new_end)?;
        Ok(())
    }

    /// Merge the VMA at `left_start` with the immediately-following VMA.
    ///
    /// # Errors
    /// - [`ENOENT`] — no VMA at `left_start`, or no adjacent
    ///   right VMA.
    /// - [`EINVAL`] — flag mismatch.
    pub fn merge_with_next(&self, left_start: usize) -> Result<(), error::Error> {
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        let (left_end, left_flags) = {
            let left = vmas.get(&left_start).ok_or(error::code::ENOENT)?;
            (left.end(), left.flags())
        };
        let right = vmas
            .get(&left_end)
            .filter(|r| r.start() == left_end)
            .ok_or(error::code::ENOENT)?;
        let right_end = right.end();
        if right.flags() != left_flags {
            return Err(error::code::EINVAL);
        }

        vmas.remove(&left_end).unwrap();
        vmas.get_mut(&left_start).unwrap().set_end(right_end)?;
        Ok(())
    }

    /// Split the VMA at `start` into two: `[start, addr)` and `[addr, old_end)`.
    ///
    /// # Errors
    /// - [`ENOENT`] — no VMA at `start`.
    /// - [`EINVAL`] — `addr` is not strictly interior (`<= start` or `>= old_end`).
    pub fn split_at(&self, start: usize, addr: usize) -> Result<(), error::Error> {
        let mut vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        // Validate everything first; only then mutate, so any failure leaves
        // the tree untouched.
        let (old_end, flags) = {
            let vma = vmas.get(&start).ok_or(error::code::ENOENT)?;
            (vma.end(), vma.flags())
        };
        if addr <= start || addr >= old_end {
            return Err(error::code::EINVAL);
        }
        let right = Vma::new(addr, old_end, flags)?;

        vmas.insert(addr, right);
        vmas.get_mut(&start).unwrap().set_end(addr)?;
        Ok(())
    }

    /// Return a snapshot of the [`Vma`] covering `addr`, if any.
    pub fn find_containing(&self, addr: usize) -> Option<Vma> {
        let vmas = self.lock.lock_guard(&self.vmas);
        vmas.range(..=addr)
            .next_back()
            .map(|(_, vma)| *vma)
            .filter(|vma| vma.contains(addr))
    }

    /// Invoke `f` for every VMA in ascending start-address order.
    pub fn for_each<F: FnMut(Vma)>(&self, mut f: F) {
        let vmas = self.lock.lock_guard(&self.vmas);
        assert_not_reentrant!(self);
        for vma in vmas.values() {
            f(*vma);
        }
    }

    pub fn is_empty(&self) -> bool {
        let vmas = self.lock.lock_guard(&self.vmas);
        vmas.is_empty()
    }

    pub fn count(&self) -> usize {
        let vmas = self.lock.lock_guard(&self.vmas);
        vmas.len()
    }

    /// `true` if a `[start, end)` range would overlap any existing VMA.
    /// Caller holds the tree lock. `start` is the BTreeMap key
    fn overlaps(vmas: &BTreeMap<usize, Vma>, start: usize, end: usize) -> bool {
        if let Some((_, prev)) = vmas.range(..=start).next_back() {
            if prev.end() > start {
                return true;
            }
        }
        if vmas.range(start..end).next().is_some() {
            return true;
        }
        false
    }
}

impl Default for AddressSpace {
    fn default() -> Self {
        Self::new()
    }
}

impl core::fmt::Debug for AddressSpace {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let count = self.count();
        f.debug_struct("AddressSpace")
            .field("vma_count", &count)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    /// Build a VMA spanning `[start, end)`. Addresses are arbitrary — no
    /// alignment is imposed — so call sites pass the `end` explicitly rather
    /// than a page count.
    fn vma(start: usize, end: usize, flags: MmapFlags) -> Vma {
        Vma::new(start, end, flags).unwrap()
    }

    #[test]
    fn vma_basic() {
        let v = Vma::new(0x1000, 0x3000, MmapFlags::READ | MmapFlags::WRITE).unwrap();
        assert_eq!(v.start(), 0x1000);
        assert_eq!(v.end(), 0x3000);
        assert_eq!(v.len(), 0x2000);
        assert!(v.flags().contains(MmapFlags::READ));
        assert!(v.flags().contains(MmapFlags::WRITE));
        assert!(!v.flags().contains(MmapFlags::EXECUTE));
        assert!(v.contains(0x1000));
        assert!(v.contains(0x2fff));
        assert!(!v.contains(0x3000));

        // Empty range.
        assert!(Vma::new(0x1000, 0x1000, MmapFlags::READ).is_err());
        // Inverted range.
        assert!(Vma::new(0x3000, 0x1000, MmapFlags::READ).is_err());
        // Non-page-aligned ranges are now legal (the invariant was removed).
        assert!(Vma::new(0x1, 0x3, MmapFlags::READ).is_ok());
        assert!(Vma::new(0x1000, 0x1001, MmapFlags::READ).is_ok());

        // Mutators. `set_end`/`set_start`/`set_flags` validate ordering only.
        let mut v = Vma::new(0x1000, 0x3000, MmapFlags::READ).unwrap();
        assert!(v.set_end(0x4000).is_ok());
        assert_eq!(v.end(), 0x4000);
        // Shrinking below `start` or to `start` is rejected.
        assert!(v.set_end(0x1000).is_err());
        // Non-page-aligned `end` is now accepted.
        assert!(v.set_end(0x4001).is_ok());
        assert_eq!(v.end(), 0x4001);
        // `set_start` keeps ordering.
        assert!(v.set_start(0x2000).is_ok());
        assert_eq!(v.start(), 0x2000);
        assert!(v.set_start(v.end()).is_err());
        // Non-page-aligned `start` is now accepted.
        assert!(v.set_start(0x2001).is_ok());
        assert_eq!(v.start(), 0x2001);
        v.set_flags(MmapFlags::WRITE);
        assert!(v.flags().contains(MmapFlags::WRITE));
    }

    #[test]
    fn address_space_starts_empty() {
        let aspace = AddressSpace::new();
        assert!(aspace.is_empty());
        assert_eq!(aspace.count(), 0);
        assert!(aspace.find_containing(0x1000).is_none());
    }

    #[test]
    fn address_space_insert_find() {
        let aspace = AddressSpace::new();
        aspace.insert(vma(0x0000, 0x2000, MmapFlags::READ)).unwrap();
        aspace
            .insert(vma(0x5000, 0x6000, MmapFlags::READ | MmapFlags::WRITE))
            .unwrap();
        aspace
            .insert(vma(0x9000, 0xc000, MmapFlags::READ | MmapFlags::EXECUTE))
            .unwrap();
        assert_eq!(aspace.count(), 3);

        assert_eq!(aspace.find_containing(0x0).unwrap().start(), 0x0000);
        assert_eq!(aspace.find_containing(0x1fff).unwrap().start(), 0x0000);
        assert_eq!(aspace.find_containing(0x5000).unwrap().start(), 0x5000);
        assert_eq!(aspace.find_containing(0xbfff).unwrap().start(), 0x9000);

        // A gap between VMAs returns None.
        assert!(aspace.find_containing(0x4000).is_none());
        // Just past the last VMA returns None.
        assert!(aspace.find_containing(0xc000).is_none());
    }

    #[test]
    fn address_space_rejects_overlap() {
        let aspace = AddressSpace::new();
        aspace
            .insert(vma(0x10000, 0x14000, MmapFlags::READ))
            .unwrap();

        // Shares a start -> overlap -> EEXIST.
        let dup = vma(0x10000, 0x11000, MmapFlags::READ);
        assert_eq!(aspace.insert(dup), Err(error::code::EEXIST));
        // Begins inside the existing VMA -> overlap.
        assert!(aspace
            .insert(vma(0x11000, 0x12000, MmapFlags::READ))
            .is_err());
        // Begins before and extends into the existing VMA -> overlap.
        assert!(aspace
            .insert(vma(0xf000, 0x13000, MmapFlags::READ))
            .is_err());
        // Adjacent (not overlapping) is fine.
        aspace
            .insert(vma(0x14000, 0x15000, MmapFlags::READ))
            .unwrap();

        assert_eq!(aspace.count(), 2);
    }

    #[test]
    fn address_space_remove() {
        let aspace = AddressSpace::new();
        aspace
            .insert(vma(0x20000, 0x28000, MmapFlags::READ))
            .unwrap();
        aspace
            .insert(vma(0x28000, 0x30000, MmapFlags::WRITE))
            .unwrap();

        let removed = aspace.remove(0x20000);
        assert_eq!(removed.map(|v| v.start()), Some(0x20000));
        assert_eq!(aspace.count(), 1);
        assert!(aspace.find_containing(0x20000).is_none());
        assert_eq!(aspace.find_containing(0x28000).unwrap().start(), 0x28000);

        // Removing a missing start is a no-op.
        assert!(aspace.remove(0xdeadb000).is_none());
        assert_eq!(aspace.count(), 1);
    }

    #[test]
    fn address_space_for_each() {
        let aspace = AddressSpace::new();
        aspace
            .insert(vma(0x30000, 0x31000, MmapFlags::READ))
            .unwrap();
        aspace
            .insert(vma(0x10000, 0x11000, MmapFlags::READ))
            .unwrap();
        aspace
            .insert(vma(0x20000, 0x21000, MmapFlags::READ))
            .unwrap();

        let mut starts = alloc::vec::Vec::new();
        aspace.for_each(|v| starts.push(v.start()));
        assert_eq!(starts, alloc::vec![0x10000, 0x20000, 0x30000]);

        // Snapshots are owned: retaining them past the closure is legal.
        let mut ends = alloc::vec::Vec::new();
        let mut retained = alloc::vec::Vec::new();
        aspace.for_each(|v| {
            ends.push(v.end());
            retained.push(v);
        });
        assert_eq!(ends, alloc::vec![0x11000, 0x21000, 0x31000]);
        assert_eq!(retained.len(), 3);
    }

    #[test]
    fn address_space_for_each_reentrancy_detected_by_nesting() {
        let aspace = AddressSpace::new();
        aspace.insert(vma(0x1000, 0x2000, MmapFlags::READ)).unwrap();
        // Outside any lock: nesting_count is 0, not recursively held.
        assert_eq!(aspace.lock.count(), 0);
        assert!(!aspace.lock.is_recursively_held());
        // Inside `for_each` the lock is held at depth 1. The closure reads
        // the live nesting count via the mutex's own spinlock — this does
        // *not* call `lock_guard` on the tree mutex, so it neither recurses
        // the tree lock nor trips `assert_not_reentrant!`. It verifies the
        // observable precondition a re-entrant method's assert would check:
        // depth is exactly 1 while iterating (not > 1, because `for_each`
        // itself does not recurse).
        aspace.for_each(|_| {
            assert_eq!(aspace.lock.count(), 1);
            assert!(!aspace.lock.is_recursively_held());
        });
        // Lock released on `for_each` exit; the space is usable afterwards.
        assert_eq!(aspace.lock.count(), 0);
        aspace.remove(0x1000);
        assert!(aspace.is_empty());
    }

    #[test]
    fn address_space_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<AddressSpace>();
    }

    #[test]
    fn address_space_reserve_basic() {
        let aspace = AddressSpace::new();
        let v = aspace
            .reserve(0x1000, 0x3000, MmapFlags::READ | MmapFlags::WRITE)
            .unwrap();
        let (vs, ve, vf) = (v.start(), v.end(), v.flags());
        assert_eq!(vs, 0x1000);
        assert_eq!(ve, 0x3000);
        assert!(vf.contains(MmapFlags::READ));
        assert!(vf.contains(MmapFlags::WRITE));
        assert!(!vf.contains(MmapFlags::EXECUTE));
        assert_eq!(aspace.count(), 1);
        // The reserved range is findable as a VMA.
        assert_eq!(aspace.find_containing(vs).unwrap().start(), vs);
    }

    #[test]
    fn address_space_reserve_fits_between() {
        let aspace = AddressSpace::new();
        // Two occupying VMAs; a free gap sits between them.
        aspace.insert(vma(0x1000, 0x2000, MmapFlags::READ)).unwrap();
        aspace.insert(vma(0x3000, 0x4000, MmapFlags::READ)).unwrap();
        // Reserve exactly the gap [0x2000, 0x3000).
        let v = aspace.reserve(0x2000, 0x3000, MmapFlags::READ).unwrap();
        let (vs, ve, _) = (v.start(), v.end(), v.flags());
        assert_eq!(vs, 0x2000);
        assert_eq!(ve, 0x3000);
        assert_eq!(aspace.count(), 3);
        // All three ranges are independently findable, no overlap.
        assert_eq!(aspace.find_containing(0x1000).unwrap().start(), 0x1000);
        assert_eq!(aspace.find_containing(0x2000).unwrap().start(), 0x2000);
        assert_eq!(aspace.find_containing(0x3000).unwrap().start(), 0x3000);
    }

    #[test]
    fn address_space_reserve_rejects_empty_range() {
        let aspace = AddressSpace::new();
        // `start >= end` is rejected by `Vma::new` as EINVAL.
        assert_eq!(
            aspace.reserve(0x1000, 0x1000, MmapFlags::READ).err(),
            Some(error::code::EINVAL)
        );
        // Inverted range likewise.
        assert_eq!(
            aspace.reserve(0x3000, 0x1000, MmapFlags::READ).err(),
            Some(error::code::EINVAL)
        );
        assert!(aspace.is_empty());
    }

    #[test]
    fn address_space_reserve_rejects_overlap() {
        let aspace = AddressSpace::new();
        aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        // Overlapping range → EEXIST.
        assert_eq!(
            aspace.reserve(0x1500, 0x2500, MmapFlags::READ).err(),
            Some(error::code::EEXIST)
        );
        assert_eq!(aspace.count(), 1);
    }

    #[test]
    fn address_space_reserve_then_remove() {
        let aspace = AddressSpace::new();
        let v = aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        let first_start = v.start();
        assert_eq!(aspace.count(), 1);

        aspace.remove(first_start);
        assert!(aspace.is_empty());

        // Re-reserve the same range → succeeds at the same address.
        let v2 = aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        assert_eq!(v2.start(), first_start);
        assert_eq!(aspace.count(), 1);
    }

    #[test]
    fn address_space_extend_up_grows_unbacked() {
        let aspace = AddressSpace::new();
        let v = aspace
            .reserve(0x1000, 0x2000, MmapFlags::READ | MmapFlags::WRITE)
            .unwrap();
        let (vs, ve, _) = (v.start(), v.end(), v.flags());
        // Grow; key (start) unchanged, count unchanged.
        let new_end = ve + 0x1000;
        aspace.extend_up(vs, new_end).unwrap();
        // `v` is a stale snapshot; re-lookup to see the grown end.
        let ve2 = aspace.find_containing(vs).unwrap().end();
        assert_eq!(ve2, new_end);
        assert_eq!(aspace.count(), 1);
        // The grown range is findable.
        assert_eq!(aspace.find_containing(new_end - 1).unwrap().start(), vs);
        // No new node was added.
        assert_eq!(aspace.count(), 1);
        aspace.remove(vs);
    }

    #[test]
    fn address_space_extend_up_rejects_overlap() {
        let aspace = AddressSpace::new();
        let a = aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        let (as_, ae, _) = (a.start(), a.end(), a.flags());
        // Place a second VMA right after `a`.
        let b = aspace.reserve(0x2000, 0x3000, MmapFlags::READ).unwrap();
        let (bs, _, _) = (b.start(), b.end(), b.flags());
        assert_eq!(bs, ae); // adjacent
                            // Extending `a` into `b` must fail.
        assert_eq!(aspace.extend_up(as_, bs + 1), Err(error::code::EINVAL));
        // `a` is unchanged on failure.
        assert_eq!(aspace.find_containing(as_).unwrap().end(), ae);
        aspace.remove(as_);
        aspace.remove(bs);
    }

    #[test]
    fn address_space_merge_with_next_same_flags() {
        let aspace = AddressSpace::new();
        // Two adjacent same-flag VMAs.
        let a = aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        let (as_, ae, _) = (a.start(), a.end(), a.flags());
        let b = aspace.reserve(0x2000, 0x3000, MmapFlags::READ).unwrap();
        let (bs, be, _) = (b.start(), b.end(), b.flags());
        assert_eq!(bs, ae); // adjacency
        assert_eq!(aspace.count(), 2);

        aspace.merge_with_next(as_).unwrap();
        // One VMA now spans both; count drops by 1.
        assert_eq!(aspace.count(), 1);
        let m = aspace.find_containing(as_).unwrap();
        assert_eq!(m.start(), as_);
        assert_eq!(m.end(), be); // merged end == right's old end
                                 // The right VMA's start is no longer a separate node.
        assert!(aspace.find_containing(bs).is_none_or(|n| n.start() == as_));
        aspace.remove(as_);
    }

    #[test]
    fn address_space_merge_with_next_rejects_flag_mismatch() {
        let aspace = AddressSpace::new();
        let a = aspace.reserve(0x1000, 0x2000, MmapFlags::READ).unwrap();
        let (as_, _, _) = (a.start(), a.end(), a.flags());
        let b = aspace.reserve(0x2000, 0x3000, MmapFlags::WRITE).unwrap();
        let (bs, _, _) = (b.start(), b.end(), b.flags());
        assert_eq!(aspace.merge_with_next(as_), Err(error::code::EINVAL));
        // Both VMAs intact on failure.
        assert_eq!(aspace.count(), 2);
        assert!(aspace.find_containing(bs).is_some());
        aspace.remove(as_);
        aspace.remove(bs);
    }

    #[test]
    fn address_space_merge_with_next_rejects_gap() {
        let aspace = AddressSpace::new();
        // Two VMAs with a gap between them.
        aspace
            .insert(vma(0x10000, 0x11000, MmapFlags::READ))
            .unwrap();
        aspace
            .insert(vma(0x20000, 0x21000, MmapFlags::READ))
            .unwrap();
        // 0x11000 != 0x20000 → not adjacent.
        assert_eq!(aspace.merge_with_next(0x10000), Err(error::code::ENOENT));
        assert_eq!(aspace.count(), 2);
        aspace.remove(0x10000);
        aspace.remove(0x20000);
    }

    #[test]
    fn address_space_split_at_interior() {
        let aspace = AddressSpace::new();
        let v = aspace.reserve(0x1000, 0x5000, MmapFlags::READ).unwrap();
        let (vs, ve, vf) = (v.start(), v.end(), v.flags());
        let split = vs + 0x2000;
        aspace.split_at(vs, split).unwrap();
        // Two VMAs now; left shrunk to [vs, split), right [split, ve).
        assert_eq!(aspace.count(), 2);
        let l = aspace.find_containing(vs).unwrap();
        assert_eq!(l.start(), vs);
        assert_eq!(l.end(), split);
        assert_eq!(l.flags(), vf);
        let r = aspace.find_containing(split).unwrap();
        assert_eq!(r.start(), split);
        assert_eq!(r.end(), ve);
        assert_eq!(r.flags(), vf);
        // The boundary: just left of `split` is the left VMA.
        assert_eq!(aspace.find_containing(split - 1).unwrap().start(), vs);
        aspace.remove(vs);
        aspace.remove(split);
    }

    #[test]
    fn address_space_split_at_rejects_boundary() {
        let aspace = AddressSpace::new();
        let v = aspace.reserve(0x1000, 0x3000, MmapFlags::READ).unwrap();
        let (vs, ve, _) = (v.start(), v.end(), v.flags());
        // `addr == start` or `addr == end` are not interior.
        assert_eq!(aspace.split_at(vs, vs), Err(error::code::EINVAL));
        assert_eq!(aspace.split_at(vs, ve), Err(error::code::EINVAL));
        // A non-page-aligned but strictly-interior `addr` is now valid.
        aspace.split_at(vs, vs + 1).unwrap();
        assert_eq!(aspace.count(), 2);
        aspace.remove(vs);
        aspace.remove(vs + 1);
    }
}
