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

use super::local_context::PreemptLease;
use crate::{
    support::DisableInterruptGuard,
    types::{IntrusiveAdapter, NestedAdapter},
};
use core::{
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
};

core::cfg_select! {
    smp => {
        use crate::types::{IRwLock, RwLock, RwLockReadGuard as ReadGuard, RwLockWriteGuard as WriteGuard};
    }
    _ => {
        use blueos_infra::local_rwlock::{LocalRwLock as RwLock, ReadGuard, WriteGuard};
    }
}

/// Only SMP can make progress by spinning on a competing guard.
#[inline(always)]
fn acquire<G>(mut attempt: impl FnMut() -> Option<G>, _conflict: &'static str) -> G {
    core::cfg_select! {
        smp => {
            loop {
                if let Some(guard) = attempt() {
                    break guard;
                }
                core::hint::spin_loop();
            }
        }
        _ => attempt().expect(_conflict),
    }
}

#[derive(Debug)]
pub struct SpinLock<T: ?Sized> {
    lock: RwLock<T>,
}
// SAFETY: ownership of the protected value can transfer iff T can.
unsafe impl<T: ?Sized + Send> Send for SpinLock<T> {}
// SAFETY: SMP uses atomic exclusion; UP state transitions are protected by
// kernel IRQ leases. Readers share &T and writers may replace T.
unsafe impl<T: ?Sized + Send + Sync> Sync for SpinLock<T> {}

pub type SpinLockWriteGuard<'a, T> = SpinLockGuard<'a, T>;
#[derive(Debug)]
#[must_use]
pub struct SpinLockGuard<'a, T: ?Sized> {
    lock_guard: ManuallyDrop<WriteGuard<'a, T>>,
    _preempt: PreemptLease,
}
// SAFETY: shared access exposes only &T; mutation and release need ownership
// or &mut Guard. Preserve the existing conservative bound.
unsafe impl<T: ?Sized + Send + Sync> Sync for SpinLockGuard<'_, T> {}

#[derive(Debug)]
#[must_use]
enum ReadProtection {
    Plain { _lease: PreemptLease },
    Irq { _guard: DisableInterruptGuard },
}

#[derive(Debug)]
#[must_use]
pub struct SpinLockReadGuard<'a, T: ?Sized> {
    lock_guard: ManuallyDrop<ReadGuard<'a, T>>,
    protection: ReadProtection,
}
// SAFETY: sharing the guard exposes only &T.
unsafe impl<T: ?Sized + Sync> Sync for SpinLockReadGuard<'_, T> {}
impl<T: ?Sized> Deref for SpinLockGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.lock_guard
    }
}
impl<T: ?Sized> DerefMut for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.lock_guard
    }
}
impl<T: ?Sized> Deref for SpinLockReadGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.lock_guard
    }
}
impl<T: ?Sized> Drop for SpinLockGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        // On UP the borrow count must be updated with kernel IRQs masked.
        #[cfg(not(smp))]
        let _irq = DisableInterruptGuard::new();
        unsafe {
            ManuallyDrop::drop(&mut self.lock_guard);
        }
    }
}
impl<T: ?Sized> Drop for SpinLockReadGuard<'_, T> {
    #[inline(always)]
    fn drop(&mut self) {
        #[cfg(not(smp))]
        let _irq = matches!(self.protection, ReadProtection::Plain { .. })
            .then(DisableInterruptGuard::new);
        unsafe {
            ManuallyDrop::drop(&mut self.lock_guard);
        }
    }
}
impl<T> SpinLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            lock: RwLock::new(data),
        }
    }
}
impl<T: ?Sized> SpinLock<T> {
    #[inline(always)]
    pub fn try_irqsave_lock(&self) -> Option<OwnedIrqSpinLockGuard<'_, T>> {
        let irq_guard = DisableInterruptGuard::new();
        // SAFETY: the IRQ mask protects the UP borrow count through guard release.
        let lock_guard = unsafe { self.lock.try_write()? };
        Some(OwnedIrqSpinLockGuard {
            lock_guard,
            irq_guard,
        })
    }
    #[inline(always)]
    pub fn try_lock(&self) -> Option<SpinLockGuard<'_, T>> {
        let irq = DisableInterruptGuard::new();
        let preempt = PreemptLease::new_with(&irq);
        #[cfg(smp)]
        drop(irq);
        // SAFETY: on UP, irq protects acquisition and SpinLockGuard masks IRQs on drop.
        let g = unsafe { self.lock.try_write()? };
        Some(SpinLockGuard {
            lock_guard: ManuallyDrop::new(g),
            _preempt: preempt,
        })
    }
    #[inline(always)]
    pub fn try_irqsave_read(&self) -> Option<SpinLockReadGuard<'_, T>> {
        let irq_guard = DisableInterruptGuard::new();
        let g = unsafe { self.lock.try_read()? };
        Some(SpinLockReadGuard {
            lock_guard: ManuallyDrop::new(g),
            protection: ReadProtection::Irq { _guard: irq_guard },
        })
    }
    #[inline(always)]
    pub fn try_read(&self) -> Option<SpinLockReadGuard<'_, T>> {
        let irq = DisableInterruptGuard::new();
        let preempt = PreemptLease::new_with(&irq);
        #[cfg(smp)]
        drop(irq);
        // SAFETY: on UP, irq protects acquisition and the plain guard masks IRQs on drop.
        let g = unsafe { self.lock.try_read()? };
        Some(SpinLockReadGuard {
            lock_guard: ManuallyDrop::new(g),
            protection: ReadProtection::Plain { _lease: preempt },
        })
    }
    #[inline(always)]
    pub fn lock(&self) -> SpinLockGuard<'_, T> {
        acquire(|| self.try_lock(), "conflicting UP lock borrow")
    }
    /// Takes a write guard that owns the local IRQ mask through unlock.
    #[inline]
    pub fn irqsave_lock(&self) -> OwnedIrqSpinLockGuard<'_, T> {
        core::cfg_select! {
            smp => acquire(|| self.try_irqsave_lock(), "conflicting UP IRQ lock borrow"),
            _ => {
                let irq_guard = DisableInterruptGuard::new();
                // SAFETY: the IRQ mask protects the UP borrow count through guard release.
                let lock_guard = unsafe { self.lock.try_write() }.expect("conflicting UP IRQ lock borrow");
                OwnedIrqSpinLockGuard { lock_guard, irq_guard }
            },
        }
    }
    #[inline(always)]
    pub fn read(&self) -> SpinLockReadGuard<'_, T> {
        acquire(|| self.try_read(), "conflicting UP read borrow")
    }
    #[inline(always)]
    pub fn irqsave_read(&self) -> SpinLockReadGuard<'_, T> {
        acquire(|| self.try_irqsave_read(), "conflicting UP IRQ read borrow")
    }
    #[inline(always)]
    pub fn write(&self) -> SpinLockWriteGuard<'_, T> {
        self.lock()
    }
    #[inline(always)]
    pub fn try_write(&self) -> Option<SpinLockWriteGuard<'_, T>> {
        self.try_lock()
    }
    #[inline(always)]
    pub fn irqsave_write(&self) -> OwnedIrqSpinLockGuard<'_, T> {
        self.irqsave_lock()
    }
    #[inline(always)]
    pub fn try_irqsave_write(&self) -> Option<OwnedIrqSpinLockGuard<'_, T>> {
        self.try_irqsave_lock()
    }
    pub fn reader_count(&self) -> usize {
        core::cfg_select! {
            smp => self.lock.reader_count() as usize,
            _ => {
                let _irq = DisableInterruptGuard::new();
                // SAFETY: the local IRQ mask serializes UP borrow-state access.
                unsafe { self.lock.reader_count() }
            }
        }
    }
    pub fn writer_count(&self) -> usize {
        core::cfg_select! {
            smp => self.lock.writer_count() as usize,
            _ => {
                let _irq = DisableInterruptGuard::new();
                // SAFETY: the local IRQ mask serializes UP borrow-state access.
                unsafe { self.lock.writer_count() }
            }
        }
    }
}

#[derive(Default, Debug)]
struct ISpinLockOffset<T: Sized, A: const IntrusiveAdapter<T>>(PhantomData<T>, PhantomData<A>);
impl<T: Sized, A: const IntrusiveAdapter<T>> const IntrusiveAdapter<ISpinLock<T, A>>
    for ISpinLockOffset<T, A>
{
    fn offset() -> usize {
        core::mem::offset_of!(ISpinLock<T, A>, lock)
    }
}

#[derive(Debug)]
pub struct ISpinLock<T: Sized, A: const IntrusiveAdapter<T>> {
    #[allow(clippy::type_complexity)]
    #[cfg(smp)]
    lock: IRwLock<T, NestedAdapter<T, A, Self, ISpinLockOffset<T, A>>>,
    #[cfg(not(smp))]
    lock: RwLock<()>,
    _adapter: PhantomData<(T, A)>,
}

impl<T: Sized, A: const IntrusiveAdapter<T>> Default for ISpinLock<T, A> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Sized, A: const IntrusiveAdapter<T>> ISpinLock<T, A> {
    pub const fn new() -> Self {
        Self {
            lock: core::cfg_select! {
                smp => IRwLock::new(),
                _ => RwLock::new(()),
            },
            _adapter: PhantomData,
        }
    }
    #[inline(always)]
    pub fn irqsave_lock(&self) -> OwnedIrqSpinLockGuard<'_, T> {
        let irq_guard = DisableInterruptGuard::new();
        let g = core::cfg_select! {
            smp => self.lock.write(),
            _ => unsafe {
                let data = (&raw const *self)
                    .cast::<u8>()
                    .cast_mut()
                    .sub(A::offset())
                    .cast::<T>();
                self.lock
                    .project_write(data)
                    .expect("conflicting UP intrusive lock borrow")
            },
        };
        OwnedIrqSpinLockGuard {
            lock_guard: g,
            irq_guard,
        }
    }
}
unsafe impl<T: Sized + Send, A: const IntrusiveAdapter<T>> Send for ISpinLock<T, A> {}
// A write guard can move the projected T out by replacement, requiring T: Send.
// Keep the existing conservative T: Sync bound for this intrusive lock.
unsafe impl<T: Sized + Send + Sync, A: const IntrusiveAdapter<T>> Sync for ISpinLock<T, A> {}

/// Payload guard borrowing an existing IRQ proof. Dropping it only unlocks the
/// payload; the proof's owner determines when interrupts can be restored.
#[derive(Debug)]
#[must_use]
pub(crate) struct BorrowedSpinLockGuard<'a, T: ?Sized> {
    lock_guard: WriteGuard<'a, T>,
    _context: PhantomData<&'a DisableInterruptGuard>,
}
impl<T: ?Sized> Deref for BorrowedSpinLockGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.lock_guard
    }
}
impl<T: ?Sized> DerefMut for BorrowedSpinLockGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.lock_guard
    }
}
impl<T: ?Sized> SpinLock<T> {
    #[inline(always)]
    pub(crate) fn try_lock_with<'a>(
        &'a self,
        _: &'a DisableInterruptGuard,
    ) -> Option<BorrowedSpinLockGuard<'a, T>> {
        // SAFETY: the proof masks UP transitions including the guard's Drop.
        let lock_guard = unsafe { self.lock.try_write()? };
        Some(BorrowedSpinLockGuard {
            lock_guard,
            _context: PhantomData,
        })
    }
    #[inline(always)]
    pub(crate) fn lock_with<'a>(
        &'a self,
        context: &'a DisableInterruptGuard,
    ) -> BorrowedSpinLockGuard<'a, T> {
        acquire(
            || self.try_lock_with(context),
            "conflicting UP borrowed lock",
        )
    }
}
impl<T: Sized, A: const IntrusiveAdapter<T>> ISpinLock<T, A> {
    #[inline(always)]
    pub(crate) fn lock_with<'a>(
        &'a self,
        _: &'a DisableInterruptGuard,
    ) -> BorrowedSpinLockGuard<'a, T> {
        let lock_guard = core::cfg_select! {
            smp => self.lock.write(),
            _ => unsafe {
                // Existing intrusive projection remains a separate migration task.
                let data = (&raw const *self)
                    .cast::<u8>()
                    .cast_mut()
                    .sub(A::offset())
                    .cast::<T>();
                self.lock
                    .project_write(data)
                    .expect("conflicting borrowed intrusive lock")
            },
        };
        BorrowedSpinLockGuard {
            lock_guard,
            _context: PhantomData,
        }
    }
}

#[cfg(test)]
mod context_tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn mixed_read_guards_keep_their_own_irq_policy() {
        let lock = SpinLock::new(0u32);
        let initially_enabled = crate::arch::local_irq_enabled();
        for drop_irq_first in [false, true] {
            let plain = lock.read();
            let irq = lock.irqsave_read();
            assert_eq!(lock.reader_count(), 2);
            if drop_irq_first {
                drop(irq);
                assert_eq!(crate::arch::local_irq_enabled(), initially_enabled);
                assert_eq!(lock.reader_count(), 1);
                drop(plain);
            } else {
                drop(plain);
                assert!(!crate::arch::local_irq_enabled());
                assert_eq!(lock.reader_count(), 1);
                drop(irq);
            }
            assert_eq!(crate::arch::local_irq_enabled(), initially_enabled);
            assert_eq!(lock.reader_count(), 0);
            let _writer = lock.try_lock().unwrap();
            assert_eq!(lock.writer_count(), 1);
        }
    }

    #[test]
    fn borrowed_irq_guard_excludes_and_preserves_outer_mask() {
        let initially_enabled = crate::arch::local_irq_enabled();
        let a = SpinLock::new(1usize);
        let b = SpinLock::new(2usize);
        let irq = DisableInterruptGuard::new();
        let context = &irq;
        let mut ga = a.lock_with(context);
        let gb = b.lock_with(context);
        assert!(a.try_lock_with(context).is_none());
        assert!(a.try_irqsave_read().is_none());
        *ga = *gb + 1;
        drop(ga);
        assert!(!crate::arch::local_irq_enabled());
        assert_eq!(*a.lock_with(context), 3);
        drop(gb);
        drop(irq);
        assert_eq!(crate::arch::local_irq_enabled(), initially_enabled);
    }

    #[test]
    fn owned_irq_guard_keeps_lock_and_mask_until_drop() {
        let initially_enabled = crate::arch::local_irq_enabled();
        let a = SpinLock::new(0usize);
        let b = SpinLock::new(7usize);
        let waiting = a.irqsave_lock();
        let second = b.irqsave_lock();
        assert!(!crate::arch::local_irq_enabled());
        assert!(a.try_irqsave_lock().is_none());
        drop(second);
        assert!(!crate::arch::local_irq_enabled());
        assert_eq!(*b.lock_with(waiting.irq_guard()), 7);
        drop(waiting);
        assert_eq!(crate::arch::local_irq_enabled(), initially_enabled);
        assert!(a.try_irqsave_lock().is_some());
    }

    #[test]
    fn forgotten_borrowed_guard_keeps_payload_inaccessible() {
        let initially_enabled = crate::arch::local_irq_enabled();
        let a = SpinLock::new(1usize);
        let irq = DisableInterruptGuard::new();
        core::mem::forget(a.lock_with(&irq));
        drop(irq);
        assert_eq!(crate::arch::local_irq_enabled(), initially_enabled);
        assert!(a.try_irqsave_lock().is_none());
        assert!(a.try_irqsave_read().is_none());
    }
}

/// Holds an exclusive payload borrow and owns the IRQ mask needed for a wait handoff.
#[derive(Debug)]
#[must_use]
pub struct OwnedIrqSpinLockGuard<'a, T: ?Sized> {
    // Field drop order releases the payload before restoring IRQs can run the scheduler.
    lock_guard: WriteGuard<'a, T>,
    irq_guard: DisableInterruptGuard,
}
impl<T: ?Sized> Deref for OwnedIrqSpinLockGuard<'_, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.lock_guard
    }
}
impl<T: ?Sized> DerefMut for OwnedIrqSpinLockGuard<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.lock_guard
    }
}
impl<T: ?Sized> OwnedIrqSpinLockGuard<'_, T> {
    #[inline(always)]
    pub(crate) fn irq_guard(&self) -> &DisableInterruptGuard {
        &self.irq_guard
    }
}

#[cfg(all(test, not(smp)))]
mod up_tests;
