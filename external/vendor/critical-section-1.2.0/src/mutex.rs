use super::CriticalSection;
use core::cell::{Ref, RefCell, RefMut, UnsafeCell};

/// A mutex based on critical sections.
///
/// # Example
///
/// ```no_run
/// # use critical_section::Mutex;
/// # use std::cell::Cell;
///
/// static FOO: Mutex<Cell<i32>> = Mutex::new(Cell::new(42));
///
/// fn main() {
///     critical_section::with(|cs| {
///         FOO.borrow(cs).set(43);
///     });
/// }
///
/// fn interrupt_handler() {
///     let _x = critical_section::with(|cs| FOO.borrow(cs).get());
/// }
/// ```
///
///
/// # Design
///
/// [`std::sync::Mutex`] has two purposes. It converts types that are [`Send`]
/// but not [`Sync`] into types that are both; and it provides
/// [interior mutability]. `critical_section::Mutex`, on the other hand, only adds
/// `Sync`. It does *not* provide interior mutability.
///
/// This was a conscious design choice. It is possible to create multiple
/// [`CriticalSection`] tokens, either by nesting critical sections or `Copy`ing
/// an existing token. As a result, it would not be sound for [`Mutex::borrow`]
/// to return `&mut T`, because there would be nothing to prevent calling
/// `borrow` multiple times to create aliased `&mut T` references.
///
/// The solution is to include a runtime check to ensure that each resource is
/// borrowed only once. This is what `std::sync::Mutex` does. However, this is
/// a runtime cost that may not be required in all circumstances. For instance,
/// `Mutex<Cell<T>>` never needs to create `&mut T` or equivalent.
///
/// If `&mut T` is needed, the simplest solution is to use `Mutex<RefCell<T>>`,
/// which is the closest analogy to `std::sync::Mutex`. [`RefCell`] inserts the
/// exact runtime check necessary to guarantee that the `&mut T` reference is
/// unique.
///
/// To reduce verbosity when using `Mutex<RefCell<T>>`, we reimplement some of
/// `RefCell`'s methods on it directly.
///
/// ```no_run
/// # use critical_section::Mutex;
/// # use std::cell::RefCell;
///
/// static FOO: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(42));
///
/// fn main() {
///     critical_section::with(|cs| {
///         // Instead of calling this
///         let _ = FOO.borrow(cs).take();
///         // Call this
///         let _ = FOO.take(cs);
///         // `RefCell::borrow` and `RefCell::borrow_mut` are renamed to
///         // `borrow_ref` and `borrow_ref_mut` to avoid name collisions
///         let _: &mut i32 = &mut *FOO.borrow_ref_mut(cs);
///     })
/// }
/// ```
///
/// [`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
/// [interior mutability]: https://doc.rust-lang.org/reference/interior-mutability.html
#[derive(Debug)]
pub struct Mutex<T> {
    // The `UnsafeCell` is not strictly necessary here: In theory, just using `T` should
    // be fine.
    // However, without `UnsafeCell`, the compiler may use niches inside `T`, and may
    // read the niche value _without locking the mutex_. As we don't provide interior
    // mutability, this is still not violating any aliasing rules and should be perfectly
    // fine. But as the cost of adding `UnsafeCell` is very small, we add it out of
    // cautiousness, just in case the reason `T` is not `Sync` in the first place is
    // something very obscure we didn't consider.
    inner: UnsafeCell<T>,
}

impl<T> Mutex<T> {
    /// Creates a new mutex.
    #[inline]
    pub const fn new(value: T) -> Self {
        Mutex {
            inner: UnsafeCell::new(value),
        }
    }

    /// Gets a mutable reference to the contained value when the mutex is already uniquely borrowed.
    ///
    /// This does not require locking or a critical section since it takes `&mut self`, which
    /// guarantees unique ownership already. Care must be taken when using this method to
    /// **unsafely** access `static mut` variables, appropriate fences must be used to prevent
    /// unwanted optimizations.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.inner.get() }
    }

    /// Unwraps the contained value, consuming the mutex.
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }

    /// Borrows the data for the duration of the critical section.
    #[inline]
    pub fn borrow<'cs>(&'cs self, _cs: CriticalSection<'cs>) -> &'cs T {
        unsafe { &*self.inner.get() }
    }
}

impl<T> Mutex<RefCell<T>> {
    /// Borrow the data and call [`RefCell::replace`]
    ///
    /// This is equivalent to `self.borrow(cs).replace(t)`
    ///
    /// # Panics
    ///
    /// This call could panic. See the documentation for [`RefCell::replace`]
    /// for more details.
    #[inline]
    #[track_caller]
    pub fn replace<'cs>(&'cs self, cs: CriticalSection<'cs>, t: T) -> T {
        self.borrow(cs).replace(t)
    }

    /// Borrow the data and call [`RefCell::replace_with`]
    ///
    /// This is equivalent to `self.borrow(cs).replace_with(f)`
    ///
    /// # Panics
    ///
    /// This call could panic. See the documentation for
    /// [`RefCell::replace_with`] for more details.
    #[inline]
    #[track_caller]
    pub fn replace_with<'cs, F>(&'cs self, cs: CriticalSection<'cs>, f: F) -> T
    where
        F: FnOnce(&mut T) -> T,
    {
        self.borrow(cs).replace_with(f)
    }

    /// Borrow the data and call [`RefCell::borrow`]
    ///
    /// This is equivalent to `self.borrow(cs).borrow()`
    ///
    /// # Panics
    ///
    /// This call could panic. See the documentation for [`RefCell::borrow`]
    /// for more details.
    #[inline]
    #[track_caller]
    pub fn borrow_ref<'cs>(&'cs self, cs: CriticalSection<'cs>) -> Ref<'cs, T> {
        self.borrow(cs).borrow()
    }

    /// Borrow the data and call [`RefCell::borrow_mut`]
    ///
    /// This is equivalent to `self.borrow(cs).borrow_mut()`
    ///
    /// # Panics
    ///
    /// This call could panic. See the documentation for [`RefCell::borrow_mut`]
    /// for more details.
    #[inline]
    #[track_caller]
    pub fn borrow_ref_mut<'cs>(&'cs self, cs: CriticalSection<'cs>) -> RefMut<'cs, T> {
        self.borrow(cs).borrow_mut()
    }
}

impl<T: Default> Mutex<RefCell<T>> {
    /// Borrow the data and call [`RefCell::take`]
    ///
    /// This is equivalent to `self.borrow(cs).take()`
    ///
    /// # Panics
    ///
    /// This call could panic. See the documentation for [`RefCell::take`]
    /// for more details.
    #[inline]
    #[track_caller]
    pub fn take<'cs>(&'cs self, cs: CriticalSection<'cs>) -> T {
        self.borrow(cs).take()
    }
}

// NOTE A `Mutex` can be used as a channel so the protected data must be `Send`
// to prevent sending non-Sendable stuff (e.g. access tokens) across different
// threads.
unsafe impl<T> Sync for Mutex<T> where T: Send {}

/// ``` compile_fail
/// fn bad(cs: critical_section::CriticalSection) -> &u32 {
///     let x = critical_section::Mutex::new(42u32);
///     x.borrow(cs)
/// }
/// ```
#[cfg(doctest)]
const BorrowMustNotOutliveMutexTest: () = ();
