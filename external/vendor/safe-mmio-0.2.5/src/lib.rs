// Copyright 2025 The safe-mmio Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

//! Types for safe MMIO device access, especially in systems with an MMU.

#![no_std]
#![deny(clippy::undocumented_unsafe_blocks)]
#![deny(unsafe_op_in_unsafe_fn)]
#![feature(const_nonnull_new)]

#[cfg(target_arch = "aarch64")]
mod aarch64_mmio;
pub mod fields;
mod physical;
#[cfg(not(target_arch = "aarch64"))]
mod volatile_mmio;

use crate::fields::{ReadOnly, ReadPure, ReadPureWrite, ReadWrite, WriteOnly};
use core::{array, fmt::Debug, marker::PhantomData, ops::Deref, ptr, ptr::NonNull};
pub use physical::PhysicalInstance;
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// A unique owned pointer to the registers of some MMIO device.
///
/// It is guaranteed to be valid and unique; no other access to the MMIO space of the device may
/// happen for the lifetime `'a`.
///
/// A `UniqueMmioPointer` may be created from a mutable reference, but this should only be used for
/// testing purposes, as references should never be constructed for real MMIO address space.
pub struct UniqueMmioPointer<'a, T: ?Sized>(SharedMmioPointer<'a, T>);

// Implement Debug, Eq and PartialEq manually rather than deriving to avoid an unneccessary bound on
// T.

impl<T: ?Sized> Debug for UniqueMmioPointer<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("UniqueMmioPointer")
            .field(&self.0.regs)
            .finish()
    }
}

impl<T: ?Sized> PartialEq for UniqueMmioPointer<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: ?Sized> Eq for UniqueMmioPointer<'_, T> {}

impl<T: ?Sized> UniqueMmioPointer<'_, T> {
    /// Creates a new `UniqueMmioPointer` from a non-null raw pointer.
    ///
    /// # Safety
    ///
    /// `regs` must be a properly aligned and valid pointer to some MMIO address space of type T,
    /// which is mapped as device memory and valid to read and write from any thread with volatile
    /// operations. There must not be any other aliases which are used to access the same MMIO
    /// region while this `UniqueMmioPointer` exists.
    ///
    /// If `T` contains any fields wrapped in [`ReadOnly`], [`WriteOnly`] or [`ReadWrite`] then they
    /// must indeed be safe to perform MMIO reads or writes on.
    pub const unsafe fn new(regs: NonNull<T>) -> Self {
        Self(SharedMmioPointer {
            regs,
            phantom: PhantomData,
        })
    }

    /// Creates a new `UniqueMmioPointer` with the same lifetime as this one.
    ///
    /// This is used internally by the [`field!`] macro and shouldn't be called directly.
    ///
    /// # Safety
    ///
    /// `regs` must be a properly aligned and valid pointer to some MMIO address space of type T,
    /// within the allocation that `self` points to.
    pub const unsafe fn child<U: ?Sized>(&mut self, regs: NonNull<U>) -> UniqueMmioPointer<U> {
        UniqueMmioPointer(SharedMmioPointer {
            regs,
            phantom: PhantomData,
        })
    }

    /// Returns a raw mut pointer to the MMIO registers.
    pub const fn ptr_mut(&mut self) -> *mut T {
        self.0.regs.as_ptr()
    }

    /// Returns a `NonNull<T>` pointer to the MMIO registers.
    pub const fn ptr_nonnull(&mut self) -> NonNull<T> {
        self.0.regs
    }

    /// Returns a new `UniqueMmioPointer` with a lifetime no greater than this one.
    pub const fn reborrow(&mut self) -> UniqueMmioPointer<T> {
        let ptr = self.ptr_nonnull();
        // SAFETY: `ptr` must be properly aligned and valid and within our allocation because it is
        // exactly our allocation.
        unsafe { self.child(ptr) }
    }
}

impl<'a, T: ?Sized> UniqueMmioPointer<'a, T> {
    /// Creates a new `UniqueMmioPointer` with the same lifetime as this one, but not tied to the
    /// lifetime this one is borrowed for.
    ///
    /// This is used internally by the [`split_fields!`] macro and shouldn't be called directly.
    ///
    /// # Safety
    ///
    /// `regs` must be a properly aligned and valid pointer to some MMIO address space of type T,
    /// within the allocation that `self` points to. `split_child` must not be called for the same
    /// child field more than once, and the original `UniqueMmioPointer` must not be used after
    /// `split_child` has been called for one or more of its fields.
    pub const unsafe fn split_child<U: ?Sized>(
        &mut self,
        regs: NonNull<U>,
    ) -> UniqueMmioPointer<'a, U> {
        UniqueMmioPointer(SharedMmioPointer {
            regs,
            phantom: PhantomData,
        })
    }
}

impl<T: FromBytes + IntoBytes> UniqueMmioPointer<'_, ReadWrite<T>> {
    /// Performs an MMIO read of the entire `T`.
    pub fn read(&mut self) -> T {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `ReadWrite` implies that it is safe to read.
        unsafe { self.read_unsafe().0 }
    }
}

impl<T: Immutable + IntoBytes> UniqueMmioPointer<'_, ReadWrite<T>> {
    /// Performs an MMIO write of the entire `T`.
    pub fn write(&mut self, value: T) {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `ReadWrite` implies that it is safe to write.
        unsafe {
            self.write_unsafe(ReadWrite(value));
        }
    }
}

impl<T: Immutable + IntoBytes> UniqueMmioPointer<'_, ReadPureWrite<T>> {
    /// Performs an MMIO write of the entire `T`.
    pub fn write(&mut self, value: T) {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `ReadPureWrite` implies that it is safe to write.
        unsafe {
            self.write_unsafe(ReadPureWrite(value));
        }
    }
}

impl<T: FromBytes + IntoBytes> UniqueMmioPointer<'_, ReadOnly<T>> {
    /// Performs an MMIO read of the entire `T`.
    pub fn read(&mut self) -> T {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `ReadOnly` implies that it is safe to read.
        unsafe { self.read_unsafe().0 }
    }
}

impl<T: Immutable + IntoBytes> UniqueMmioPointer<'_, WriteOnly<T>> {
    /// Performs an MMIO write of the entire `T`.
    pub fn write(&mut self, value: T) {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `WriteOnly` implies that it is safe to write.
        unsafe {
            self.write_unsafe(WriteOnly(value));
        }
    }
}

impl<'a, T> UniqueMmioPointer<'a, [T]> {
    /// Returns a `UniqueMmioPointer` to an element of this slice, or `None` if the index is out of
    /// bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_mmio::{UniqueMmioPointer, fields::ReadWrite};
    ///
    /// let mut slice: UniqueMmioPointer<[ReadWrite<u32>]>;
    /// # let mut fake = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
    /// # slice = UniqueMmioPointer::from(fake.as_mut_slice());
    /// let mut element = slice.get(1).unwrap();
    /// element.write(42);
    /// ```
    pub const fn get(&mut self, index: usize) -> Option<UniqueMmioPointer<T>> {
        if index >= self.0.len() {
            return None;
        }
        // SAFETY: self.ptr_mut() is guaranteed to return a pointer that is valid for MMIO and
        // unique, as promised by the caller of `UniqueMmioPointer::new`.
        let regs = NonNull::new(unsafe { &raw mut (*self.ptr_mut())[index] }).unwrap();
        // SAFETY: We created regs from the raw slice in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        Some(unsafe { self.child(regs) })
    }

    /// Returns a `UniqueMmioPointer` to an element of this slice, or `None` if the index is out of
    /// bounds.
    ///
    /// Unlike [`UniqueMmioPointer::get`] this takes ownership of the original pointer. This is
    /// useful when you want to store the resulting pointer without keeping the original pointer
    /// around.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_mmio::{UniqueMmioPointer, fields::ReadWrite};
    ///
    /// let mut slice: UniqueMmioPointer<[ReadWrite<u32>]>;
    /// # let mut fake = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
    /// # slice = UniqueMmioPointer::from(fake.as_mut_slice());
    /// let mut element = slice.take(1).unwrap();
    /// element.write(42);
    /// // `slice` can no longer be used at this point.
    /// ```
    pub const fn take(mut self, index: usize) -> Option<UniqueMmioPointer<'a, T>> {
        if index >= self.0.len() {
            return None;
        }
        // SAFETY: self.ptr_mut() is guaranteed to return a pointer that is valid for MMIO and
        // unique, as promised by the caller of `UniqueMmioPointer::new`.
        let regs = NonNull::new(unsafe { &raw mut (*self.ptr_mut())[index] }).unwrap();
        // SAFETY: We created regs from the raw slice in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs. `self` is dropped immediately after this and we
        // don't split out any other children.
        Some(unsafe { self.split_child(regs) })
    }
}

impl<'a, T, const LEN: usize> UniqueMmioPointer<'a, [T; LEN]> {
    /// Splits a `UniqueMmioPointer` to an array into an array of `UniqueMmioPointer`s.
    pub fn split(&mut self) -> [UniqueMmioPointer<T>; LEN] {
        array::from_fn(|i| {
            UniqueMmioPointer(SharedMmioPointer {
                // SAFETY: self.regs is always unique and valid for MMIO access. We make sure the
                // pointers we split it into don't overlap, so the same applies to each of them.
                regs: NonNull::new(unsafe { &raw mut (*self.ptr_mut())[i] }).unwrap(),
                phantom: PhantomData,
            })
        })
    }

    /// Converts this array pointer to an equivalent slice pointer.
    pub const fn as_mut_slice(&mut self) -> UniqueMmioPointer<[T]> {
        let regs = NonNull::new(self.ptr_mut()).unwrap();
        // SAFETY: We created regs from the raw array in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        unsafe { self.child(regs) }
    }

    /// Returns a `UniqueMmioPointer` to an element of this array, or `None` if the index is out of
    /// bounds.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_mmio::{UniqueMmioPointer, fields::ReadWrite};
    ///
    /// let mut slice: UniqueMmioPointer<[ReadWrite<u32>; 3]>;
    /// # let mut fake = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
    /// # slice = UniqueMmioPointer::from(&mut fake);
    /// let mut element = slice.get(1).unwrap();
    /// element.write(42);
    /// slice.get(2).unwrap().write(100);
    /// ```
    pub const fn get(&mut self, index: usize) -> Option<UniqueMmioPointer<T>> {
        if index >= LEN {
            return None;
        }
        // SAFETY: self.ptr_mut() is guaranteed to return a pointer that is valid for MMIO and
        // unique, as promised by the caller of `UniqueMmioPointer::new`.
        let regs = NonNull::new(unsafe { &raw mut (*self.ptr_mut())[index] }).unwrap();
        // SAFETY: We created regs from the raw array in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        Some(unsafe { self.child(regs) })
    }

    /// Returns a `UniqueMmioPointer` to an element of this array, or `None` if the index is out of
    /// bounds.
    ///
    /// Unlike [`UniqueMmioPointer::get`] this takes ownership of the original pointer. This is
    /// useful when you want to store the resulting pointer without keeping the original pointer
    /// around.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_mmio::{UniqueMmioPointer, fields::ReadWrite};
    ///
    /// let mut array: UniqueMmioPointer<[ReadWrite<u32>; 3]>;
    /// # let mut fake = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
    /// # array = UniqueMmioPointer::from(&mut fake);
    /// let mut element = array.take(1).unwrap();
    /// element.write(42);
    /// // `array` can no longer be used at this point.
    /// ```
    pub const fn take(mut self, index: usize) -> Option<UniqueMmioPointer<'a, T>> {
        if index >= LEN {
            return None;
        }
        // SAFETY: self.ptr_mut() is guaranteed to return a pointer that is valid for MMIO and
        // unique, as promised by the caller of `UniqueMmioPointer::new`.
        let regs = NonNull::new(unsafe { &raw mut (*self.ptr_mut())[index] }).unwrap();
        // SAFETY: We created regs from the raw array in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs. `self` is dropped immediately after this and we
        // don't split out any other children.
        Some(unsafe { self.split_child(regs) })
    }
}

impl<'a, T, const LEN: usize> From<UniqueMmioPointer<'a, [T; LEN]>> for UniqueMmioPointer<'a, [T]> {
    fn from(mut value: UniqueMmioPointer<'a, [T; LEN]>) -> Self {
        let regs = NonNull::new(value.ptr_mut()).unwrap();
        // SAFETY: regs comes from a UniqueMmioPointer so already satisfies all the safety
        // requirements.
        unsafe { UniqueMmioPointer::new(regs) }
    }
}

impl<'a, T> From<UniqueMmioPointer<'a, T>> for UniqueMmioPointer<'a, [T; 1]> {
    fn from(mut value: UniqueMmioPointer<'a, T>) -> Self {
        let regs = NonNull::new(value.ptr_mut()).unwrap().cast();
        // SAFETY: regs comes from a UniqueMmioPointer so already satisfies all the safety
        // requirements.
        unsafe { UniqueMmioPointer::new(regs) }
    }
}

impl<'a, T> From<UniqueMmioPointer<'a, T>> for UniqueMmioPointer<'a, [T]> {
    fn from(mut value: UniqueMmioPointer<'a, T>) -> Self {
        let array: *mut [T; 1] = value.ptr_mut().cast();
        let regs = NonNull::new(array).unwrap();
        // SAFETY: regs comes from a UniqueMmioPointer so already satisfies all the safety
        // requirements.
        unsafe { UniqueMmioPointer::new(regs) }
    }
}

impl<'a, T, const LEN: usize> From<UniqueMmioPointer<'a, [T; LEN]>>
    for [UniqueMmioPointer<'a, T>; LEN]
{
    fn from(mut value: UniqueMmioPointer<'a, [T; LEN]>) -> Self {
        array::from_fn(|i| {
            let item_pointer = value.split()[i].ptr_mut();
            // SAFETY: `split_child` is called only once on each item and the original
            // `UniqueMmioPointer` is consumed by this function.
            unsafe { value.split_child(core::ptr::NonNull::new(item_pointer).unwrap()) }
        })
    }
}

impl<'a, T: ?Sized> From<&'a mut T> for UniqueMmioPointer<'a, T> {
    fn from(r: &'a mut T) -> Self {
        Self(SharedMmioPointer {
            regs: r.into(),
            phantom: PhantomData,
        })
    }
}

impl<'a, T: ?Sized> Deref for UniqueMmioPointer<'a, T> {
    type Target = SharedMmioPointer<'a, T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A shared pointer to the registers of some MMIO device.
///
/// It is guaranteed to be valid but unlike [`UniqueMmioPointer`] may not be unique.
pub struct SharedMmioPointer<'a, T: ?Sized> {
    regs: NonNull<T>,
    phantom: PhantomData<&'a T>,
}

// Implement Debug, Eq and PartialEq manually rather than deriving to avoid an unneccessary bound on
// T.

impl<T: ?Sized> Debug for SharedMmioPointer<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("SharedMmioPointer")
            .field(&self.regs)
            .finish()
    }
}

impl<T: ?Sized> PartialEq for SharedMmioPointer<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.regs.as_ptr(), other.regs.as_ptr())
    }
}

impl<T: ?Sized> Eq for SharedMmioPointer<'_, T> {}

impl<T: ?Sized> Clone for SharedMmioPointer<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for SharedMmioPointer<'_, T> {}

impl<'a, T: ?Sized> SharedMmioPointer<'a, T> {
    /// Creates a new `SharedMmioPointer` with the same lifetime as this one.
    ///
    /// This is used internally by the [`field_shared!`] macro and shouldn't be called directly.
    ///
    /// # Safety
    ///
    /// `regs` must be a properly aligned and valid pointer to some MMIO address space of type T,
    /// within the allocation that `self` points to.
    pub const unsafe fn child<U: ?Sized>(&self, regs: NonNull<U>) -> SharedMmioPointer<'a, U> {
        SharedMmioPointer {
            regs,
            phantom: PhantomData,
        }
    }

    /// Returns a raw const pointer to the MMIO registers.
    pub const fn ptr(&self) -> *const T {
        self.regs.as_ptr()
    }
}

// SAFETY: A `SharedMmioPointer` always originates either from a reference or from a
// `UniqueMmioPointer`. The caller of `UniqueMmioPointer::new` promises that the MMIO registers can
// be accessed from any thread.
unsafe impl<T: ?Sized + Send + Sync> Send for SharedMmioPointer<'_, T> {}

impl<'a, T: ?Sized> From<&'a T> for SharedMmioPointer<'a, T> {
    fn from(r: &'a T) -> Self {
        Self {
            regs: r.into(),
            phantom: PhantomData,
        }
    }
}

impl<'a, T: ?Sized> From<UniqueMmioPointer<'a, T>> for SharedMmioPointer<'a, T> {
    fn from(unique: UniqueMmioPointer<'a, T>) -> Self {
        unique.0
    }
}

impl<T: FromBytes + IntoBytes> SharedMmioPointer<'_, ReadPure<T>> {
    /// Performs an MMIO read of the entire `T`.
    pub fn read(&self) -> T {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space, and `T`
        // being wrapped in `ReadPure` implies that it is safe to read from a shared reference
        // because doing so has no side-effects.
        unsafe { self.read_unsafe().0 }
    }
}

impl<T: FromBytes + IntoBytes> SharedMmioPointer<'_, ReadPureWrite<T>> {
    /// Performs an MMIO read of the entire `T`.
    pub fn read(&self) -> T {
        // SAFETY: self.regs is always a valid pointer to MMIO address space, and `T`
        // being wrapped in `ReadPureWrite` implies that it is safe to read from a shared reference
        // because doing so has no side-effects.
        unsafe { self.read_unsafe().0 }
    }
}

impl<'a, T> SharedMmioPointer<'a, [T]> {
    /// Returns a `SharedMmioPointer` to an element of this slice, or `None` if the index is out of
    /// bounds.
    pub const fn get(&self, index: usize) -> Option<SharedMmioPointer<'a, T>> {
        if index >= self.len() {
            return None;
        }
        // SAFETY: self.regs is always unique and valid for MMIO access.
        let regs = NonNull::new(unsafe { &raw mut (*self.regs.as_ptr())[index] }).unwrap();
        // SAFETY: We created regs from the raw slice in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        Some(unsafe { self.child(regs) })
    }

    /// Returns the length of the slice.
    pub const fn len(&self) -> usize {
        self.regs.len()
    }

    /// Returns whether the slice is empty.
    pub const fn is_empty(&self) -> bool {
        self.regs.is_empty()
    }
}

impl<'a, T, const LEN: usize> SharedMmioPointer<'a, [T; LEN]> {
    /// Splits a `SharedMmioPointer` to an array into an array of `SharedMmioPointer`s.
    pub fn split(&self) -> [SharedMmioPointer<'a, T>; LEN] {
        array::from_fn(|i| SharedMmioPointer {
            // SAFETY: self.regs is always unique and valid for MMIO access. We make sure the
            // pointers we split it into don't overlap, so the same applies to each of them.
            regs: NonNull::new(unsafe { &raw mut (*self.regs.as_ptr())[i] }).unwrap(),
            phantom: PhantomData,
        })
    }

    /// Converts this array pointer to an equivalent slice pointer.
    pub const fn as_slice(&self) -> SharedMmioPointer<'a, [T]> {
        let regs = NonNull::new(self.regs.as_ptr()).unwrap();
        // SAFETY: We created regs from the raw array in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        unsafe { self.child(regs) }
    }

    /// Returns a `SharedMmioPointer` to an element of this array, or `None` if the index is out of
    /// bounds.
    pub const fn get(&self, index: usize) -> Option<SharedMmioPointer<'a, T>> {
        if index >= LEN {
            return None;
        }
        // SAFETY: self.regs is always unique and valid for MMIO access.
        let regs = NonNull::new(unsafe { &raw mut (*self.regs.as_ptr())[index] }).unwrap();
        // SAFETY: We created regs from the raw array in self.regs, so it must also be valid, unique
        // and within the allocation of self.regs.
        Some(unsafe { self.child(regs) })
    }
}

impl<'a, T, const LEN: usize> From<SharedMmioPointer<'a, [T; LEN]>> for SharedMmioPointer<'a, [T]> {
    fn from(value: SharedMmioPointer<'a, [T; LEN]>) -> Self {
        let regs = NonNull::new(value.regs.as_ptr()).unwrap();
        SharedMmioPointer {
            regs,
            phantom: PhantomData,
        }
    }
}

impl<'a, T> From<SharedMmioPointer<'a, T>> for SharedMmioPointer<'a, [T; 1]> {
    fn from(value: SharedMmioPointer<'a, T>) -> Self {
        let regs = NonNull::new(value.regs.as_ptr()).unwrap().cast();
        SharedMmioPointer {
            regs,
            phantom: PhantomData,
        }
    }
}

impl<'a, T> From<SharedMmioPointer<'a, T>> for SharedMmioPointer<'a, [T]> {
    fn from(value: SharedMmioPointer<'a, T>) -> Self {
        let array: *mut [T; 1] = value.regs.as_ptr().cast();
        let regs = NonNull::new(array).unwrap();
        SharedMmioPointer {
            regs,
            phantom: PhantomData,
        }
    }
}

/// Gets a `UniqueMmioPointer` to a field of a type wrapped in a `UniqueMmioPointer`.
#[macro_export]
macro_rules! field {
    ($mmio_pointer:expr, $field:ident) => {{
        // Make sure $mmio_pointer is the right type.
        let mmio_pointer: &mut $crate::UniqueMmioPointer<_> = &mut $mmio_pointer;
        // SAFETY: ptr_mut is guaranteed to return a valid pointer for MMIO, so the pointer to the
        // field must also be valid. MmioPointer::child gives it the same lifetime as the original
        // pointer.
        unsafe {
            let child_pointer =
                core::ptr::NonNull::new(&raw mut (*mmio_pointer.ptr_mut()).$field).unwrap();
            mmio_pointer.child(child_pointer)
        }
    }};
}

/// Gets `UniqueMmioPointer`s to several fields of a type wrapped in a `UniqueMmioPointer`.
///
/// # Safety
///
/// The same field name must not be passed more than once.
#[macro_export]
macro_rules! split_fields {
    ($mmio_pointer:expr, $( $field:ident ),+) => {{
        // Make sure $mmio_pointer is the right type, and take ownership of it.
        let mut mmio_pointer: $crate::UniqueMmioPointer<_> = $mmio_pointer;
        let pointer = mmio_pointer.ptr_mut();
        let ret = (
            $(
                // SAFETY: ptr_mut is guaranteed to return a valid pointer for MMIO, so the pointer
                // to the field must also be valid. MmioPointer::child gives it the same lifetime as
                // the original pointer, and the caller of `split_fields!` promised not to pass the
                // same field more than once.
                {
                    let child_pointer = core::ptr::NonNull::new(&raw mut (*pointer).$field).unwrap();
                    mmio_pointer.split_child(child_pointer)
                }
            ),+
        );
        ret
    }};
}

/// Gets a `SharedMmioPointer` to a field of a type wrapped in a `SharedMmioPointer`.
#[macro_export]
macro_rules! field_shared {
    ($mmio_pointer:expr, $field:ident) => {{
        // Make sure $mmio_pointer is the right type.
        let mmio_pointer: &$crate::SharedMmioPointer<_> = &$mmio_pointer;
        // SAFETY: ptr_mut is guaranteed to return a valid pointer for MMIO, so the pointer to the
        // field must also be valid. MmioPointer::child gives it the same lifetime as the original
        // pointer.
        unsafe {
            let child_pointer =
                core::ptr::NonNull::new((&raw const (*mmio_pointer.ptr()).$field).cast_mut())
                    .unwrap();
            mmio_pointer.child(child_pointer)
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fields() {
        #[repr(C)]
        struct Foo {
            a: ReadWrite<u32>,
            b: ReadOnly<u32>,
            c: ReadPure<u32>,
        }

        let mut foo = Foo {
            a: ReadWrite(1),
            b: ReadOnly(2),
            c: ReadPure(3),
        };
        let mut owned: UniqueMmioPointer<Foo> = UniqueMmioPointer::from(&mut foo);

        let mut owned_a: UniqueMmioPointer<ReadWrite<u32>> = field!(owned, a);
        assert_eq!(owned_a.read(), 1);
        owned_a.write(42);
        assert_eq!(owned_a.read(), 42);
        field!(owned, a).write(44);
        assert_eq!(field!(owned, a).read(), 44);

        let mut owned_b: UniqueMmioPointer<ReadOnly<u32>> = field!(owned, b);
        assert_eq!(owned_b.read(), 2);

        let owned_c: UniqueMmioPointer<ReadPure<u32>> = field!(owned, c);
        assert_eq!(owned_c.read(), 3);
        assert_eq!(field!(owned, c).read(), 3);
    }

    #[test]
    fn shared_fields() {
        #[repr(C)]
        struct Foo {
            a: ReadPureWrite<u32>,
            b: ReadPure<u32>,
        }

        let foo = Foo {
            a: ReadPureWrite(1),
            b: ReadPure(2),
        };
        let shared: SharedMmioPointer<Foo> = SharedMmioPointer::from(&foo);

        let shared_a: SharedMmioPointer<ReadPureWrite<u32>> = field_shared!(shared, a);
        assert_eq!(shared_a.read(), 1);
        assert_eq!(field_shared!(shared, a).read(), 1);

        let shared_b: SharedMmioPointer<ReadPure<u32>> = field_shared!(shared, b);
        assert_eq!(shared_b.read(), 2);
    }

    #[test]
    fn shared_from_unique() {
        #[repr(C)]
        struct Foo {
            a: ReadPureWrite<u32>,
            b: ReadPure<u32>,
        }

        let mut foo = Foo {
            a: ReadPureWrite(1),
            b: ReadPure(2),
        };
        let unique: UniqueMmioPointer<Foo> = UniqueMmioPointer::from(&mut foo);

        let shared_a: SharedMmioPointer<ReadPureWrite<u32>> = field_shared!(unique, a);
        assert_eq!(shared_a.read(), 1);

        let shared_b: SharedMmioPointer<ReadPure<u32>> = field_shared!(unique, b);
        assert_eq!(shared_b.read(), 2);
    }

    #[test]
    fn restricted_fields() {
        #[repr(C)]
        struct Foo {
            r: ReadOnly<u32>,
            w: WriteOnly<u32>,
            u: u32,
        }

        let mut foo = Foo {
            r: ReadOnly(1),
            w: WriteOnly(2),
            u: 3,
        };
        let mut owned: UniqueMmioPointer<Foo> = UniqueMmioPointer::from(&mut foo);

        let mut owned_r: UniqueMmioPointer<ReadOnly<u32>> = field!(owned, r);
        assert_eq!(owned_r.read(), 1);

        let mut owned_w: UniqueMmioPointer<WriteOnly<u32>> = field!(owned, w);
        owned_w.write(42);

        let mut owned_u: UniqueMmioPointer<u32> = field!(owned, u);
        // SAFETY: 'u' is safe to read or write because it's just a fake.
        unsafe {
            assert_eq!(owned_u.read_unsafe(), 3);
            owned_u.write_unsafe(42);
            assert_eq!(owned_u.read_unsafe(), 42);
        }
    }

    #[test]
    fn array() {
        let mut foo = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
        let mut owned = UniqueMmioPointer::from(&mut foo);

        let mut parts = owned.split();
        assert_eq!(parts[0].read(), 1);
        assert_eq!(parts[1].read(), 2);
        assert_eq!(owned.split()[2].read(), 3);
    }

    #[test]
    fn array_shared() {
        let foo = [ReadPure(1), ReadPure(2), ReadPure(3)];
        let shared = SharedMmioPointer::from(&foo);

        let parts = shared.split();
        assert_eq!(parts[0].read(), 1);
        assert_eq!(parts[1].read(), 2);
        assert_eq!(shared.split()[2].read(), 3);
    }

    #[test]
    fn slice() {
        let mut foo = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];
        let mut owned = UniqueMmioPointer::from(foo.as_mut_slice());

        assert!(!owned.ptr().is_null());
        assert!(!owned.ptr_mut().is_null());

        assert!(!owned.is_empty());
        assert_eq!(owned.len(), 3);

        let mut first: UniqueMmioPointer<ReadWrite<i32>> = owned.get(0).unwrap();
        assert_eq!(first.read(), 1);

        let mut second: UniqueMmioPointer<ReadWrite<i32>> = owned.get(1).unwrap();
        assert_eq!(second.read(), 2);

        assert!(owned.get(3).is_none());
    }

    #[test]
    fn slice_shared() {
        let foo = [ReadPure(1), ReadPure(2), ReadPure(3)];
        let shared = SharedMmioPointer::from(foo.as_slice());

        assert!(!shared.ptr().is_null());

        assert!(!shared.is_empty());
        assert_eq!(shared.len(), 3);

        let first: SharedMmioPointer<ReadPure<i32>> = shared.get(0).unwrap();
        assert_eq!(first.read(), 1);

        let second: SharedMmioPointer<ReadPure<i32>> = shared.get(1).unwrap();
        assert_eq!(second.read(), 2);

        assert!(shared.get(3).is_none());

        // Test that lifetime of pointer returned from `get` isn't tied to the lifetime of the slice
        // pointer.
        let second = {
            let shared_copy = shared;
            shared_copy.get(1).unwrap()
        };
        assert_eq!(second.read(), 2);
    }

    #[test]
    fn array_field() {
        #[repr(C)]
        struct Regs {
            a: [ReadPureWrite<u32>; 4],
        }

        let mut foo = Regs {
            a: [const { ReadPureWrite(0) }; 4],
        };
        let mut owned: UniqueMmioPointer<Regs> = UniqueMmioPointer::from(&mut foo);

        field!(owned, a).get(0).unwrap().write(42);
        assert_eq!(field_shared!(owned, a).get(0).unwrap().read(), 42);
    }

    #[test]
    fn slice_field() {
        #[repr(transparent)]
        struct Regs {
            s: [ReadPureWrite<u32>],
        }

        impl Regs {
            fn from_slice<'a>(slice: &'a mut [ReadPureWrite<u32>]) -> &'a mut Self {
                let regs_ptr: *mut Self = slice as *mut [ReadPureWrite<u32>] as *mut Self;
                // SAFETY: `Regs` is repr(transparent) so a reference to its field has the same
                // metadata as a reference to `Regs``.
                unsafe { &mut *regs_ptr }
            }
        }

        let mut foo: [ReadPureWrite<u32>; 1] = [ReadPureWrite(0)];
        let regs_mut = Regs::from_slice(foo.as_mut_slice());
        let mut owned: UniqueMmioPointer<Regs> = UniqueMmioPointer::from(regs_mut);

        field!(owned, s).get(0).unwrap().write(42);
        assert_eq!(field_shared!(owned, s).get(0).unwrap().read(), 42);
    }

    #[test]
    fn multiple_fields() {
        #[repr(C)]
        struct Regs {
            first: ReadPureWrite<u32>,
            second: ReadPureWrite<u32>,
            third: ReadPureWrite<u32>,
        }

        let mut foo = Regs {
            first: ReadPureWrite(1),
            second: ReadPureWrite(2),
            third: ReadPureWrite(3),
        };
        let mut owned: UniqueMmioPointer<Regs> = UniqueMmioPointer::from(&mut foo);

        // SAFETY: We don't pass the same field name more than once.
        let (first, second) = unsafe { split_fields!(owned.reborrow(), first, second) };

        assert_eq!(first.read(), 1);
        assert_eq!(second.read(), 2);

        drop(first);
        drop(second);

        assert_eq!(field!(owned, first).read(), 1);
    }

    #[test]
    fn split_array() {
        let mut foo = [ReadWrite(1), ReadWrite(2), ReadWrite(3)];

        let mut parts: [UniqueMmioPointer<ReadWrite<i32>>; 3] = {
            let owned = UniqueMmioPointer::from(&mut foo);

            owned.into()
        };

        assert_eq!(parts[0].read(), 1);
        assert_eq!(parts[1].read(), 2);
    }
}
