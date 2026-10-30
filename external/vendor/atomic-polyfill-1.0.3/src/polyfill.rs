pub use core::sync::atomic::{compiler_fence, fence, Ordering};

macro_rules! atomic_int {
    ($int_type:ident,$atomic_type:ident, $cfg:ident) => {
        #[cfg(not($cfg))]
        pub use core::sync::atomic::$atomic_type;

        #[cfg($cfg)]
        #[repr(transparent)]
        pub struct $atomic_type {
            inner: core::cell::UnsafeCell<$int_type>,
        }

        #[cfg($cfg)]
        unsafe impl Send for $atomic_type {}
        #[cfg($cfg)]
        unsafe impl Sync for $atomic_type {}
        #[cfg($cfg)]
        impl core::panic::RefUnwindSafe for $atomic_type {}

        #[cfg($cfg)]
        impl Default for $atomic_type {
            #[inline]
            fn default() -> Self {
                Self::new(Default::default())
            }
        }

        #[cfg($cfg)]
        impl From<$int_type> for $atomic_type {
            #[inline]
            fn from(v: $int_type) -> Self {
                Self::new(v)
            }
        }

        #[cfg($cfg)]
        impl core::fmt::Debug for $atomic_type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Debug::fmt(&self.load(Ordering::SeqCst), f)
            }
        }

        #[cfg($cfg)]
        impl $atomic_type {
            pub const fn new(v: $int_type) -> Self {
                Self {
                    inner: core::cell::UnsafeCell::new(v),
                }
            }

            pub fn into_inner(self) -> $int_type {
                self.inner.into_inner()
            }

            pub fn get_mut(&mut self) -> &mut $int_type {
                self.inner.get_mut()
            }

            pub fn load(&self, _order: Ordering) -> $int_type {
                return critical_section::with(|_| unsafe { *self.inner.get() });
            }

            pub fn store(&self, val: $int_type, _order: Ordering) {
                return critical_section::with(|_| unsafe { *self.inner.get() = val });
            }

            pub fn swap(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |_| val)
            }

            pub fn compare_exchange(
                &self,
                current: $int_type,
                new: $int_type,
                success: Ordering,
                failure: Ordering,
            ) -> Result<$int_type, $int_type> {
                self.compare_exchange_weak(current, new, success, failure)
            }

            pub fn compare_exchange_weak(
                &self,
                current: $int_type,
                new: $int_type,
                _success: Ordering,
                _failure: Ordering,
            ) -> Result<$int_type, $int_type> {
                critical_section::with(|_| {
                    let val = unsafe { &mut *self.inner.get() };
                    let old = *val;
                    if old == current {
                        *val = new;
                        Ok(old)
                    } else {
                        Err(old)
                    }
                })
            }

            pub fn fetch_add(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old.wrapping_add(val))
            }

            pub fn fetch_sub(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old.wrapping_sub(val))
            }

            pub fn fetch_and(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old & val)
            }

            pub fn fetch_nand(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| !(old & val))
            }

            pub fn fetch_or(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old | val)
            }

            pub fn fetch_xor(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old ^ val)
            }

            pub fn fetch_update<F>(
                &self,
                _set_order: Ordering,
                _fetch_order: Ordering,
                mut f: F,
            ) -> Result<$int_type, $int_type>
            where
                F: FnMut($int_type) -> Option<$int_type>,
            {
                critical_section::with(|_| {
                    let val = unsafe { &mut *self.inner.get() };
                    let old = *val;
                    if let Some(new) = f(old) {
                        *val = new;
                        Ok(old)
                    } else {
                        Err(old)
                    }
                })
            }

            pub fn fetch_max(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old.max(val))
            }

            pub fn fetch_min(&self, val: $int_type, order: Ordering) -> $int_type {
                self.op(order, |old| old.min(val))
            }

            fn op(&self, _order: Ordering, f: impl FnOnce($int_type) -> $int_type) -> $int_type {
                critical_section::with(|_| {
                    let val = unsafe { &mut *self.inner.get() };
                    let old = *val;
                    *val = f(old);
                    old
                })
            }
        }
    };
}

atomic_int!(u8, AtomicU8, polyfill_u8);
atomic_int!(u16, AtomicU16, polyfill_u16);
atomic_int!(u32, AtomicU32, polyfill_u32);
atomic_int!(u64, AtomicU64, polyfill_u64);
atomic_int!(usize, AtomicUsize, polyfill_usize);
atomic_int!(i8, AtomicI8, polyfill_i8);
atomic_int!(i16, AtomicI16, polyfill_i16);
atomic_int!(i32, AtomicI32, polyfill_i32);
atomic_int!(i64, AtomicI64, polyfill_i64);
atomic_int!(isize, AtomicIsize, polyfill_isize);

#[cfg(not(polyfill_bool))]
pub use core::sync::atomic::AtomicBool;

#[cfg(polyfill_bool)]
#[repr(transparent)]
pub struct AtomicBool {
    inner: core::cell::UnsafeCell<bool>,
}

#[cfg(polyfill_bool)]
impl Default for AtomicBool {
    /// Creates an `AtomicBool` initialized to `false`.
    #[inline]
    fn default() -> Self {
        Self::new(false)
    }
}

#[cfg(polyfill_bool)]
impl From<bool> for AtomicBool {
    #[inline]
    fn from(v: bool) -> Self {
        Self::new(v)
    }
}

#[cfg(polyfill_bool)]
impl core::fmt::Debug for AtomicBool {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.load(Ordering::SeqCst), f)
    }
}

#[cfg(polyfill_bool)]
unsafe impl Send for AtomicBool {}
#[cfg(polyfill_bool)]
unsafe impl Sync for AtomicBool {}
#[cfg(polyfill_bool)]
impl core::panic::RefUnwindSafe for AtomicBool {}

#[cfg(polyfill_bool)]
impl AtomicBool {
    pub const fn new(v: bool) -> AtomicBool {
        Self {
            inner: core::cell::UnsafeCell::new(v),
        }
    }

    pub fn into_inner(self) -> bool {
        self.inner.into_inner()
    }

    pub fn get_mut(&mut self) -> &mut bool {
        self.inner.get_mut()
    }

    pub fn load(&self, _order: Ordering) -> bool {
        critical_section::with(|_| unsafe { *self.inner.get() })
    }

    pub fn store(&self, val: bool, _order: Ordering) {
        critical_section::with(|_| unsafe { *self.inner.get() = val });
    }

    pub fn swap(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |_| val)
    }

    pub fn compare_exchange(
        &self,
        current: bool,
        new: bool,
        success: Ordering,
        failure: Ordering,
    ) -> Result<bool, bool> {
        self.compare_exchange_weak(current, new, success, failure)
    }

    pub fn compare_exchange_weak(
        &self,
        current: bool,
        new: bool,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<bool, bool> {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            if old == current {
                *val = new;
                Ok(old)
            } else {
                Err(old)
            }
        })
    }

    pub fn fetch_and(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| old & val)
    }

    pub fn fetch_nand(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| !(old & val))
    }

    pub fn fetch_or(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| old | val)
    }

    pub fn fetch_xor(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| old ^ val)
    }

    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<bool, bool>
    where
        F: FnMut(bool) -> Option<bool>,
    {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            if let Some(new) = f(old) {
                *val = new;
                Ok(old)
            } else {
                Err(old)
            }
        })
    }

    pub fn fetch_max(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| old.max(val))
    }

    pub fn fetch_min(&self, val: bool, order: Ordering) -> bool {
        self.op(order, |old| old.min(val))
    }

    fn op(&self, _order: Ordering, f: impl FnOnce(bool) -> bool) -> bool {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            *val = f(old);
            old
        })
    }
}

#[cfg(not(polyfill_ptr))]
pub use core::sync::atomic::AtomicPtr;

#[cfg(polyfill_ptr)]
#[repr(transparent)]
pub struct AtomicPtr<T> {
    inner: core::cell::UnsafeCell<*mut T>,
}

#[cfg(polyfill_ptr)]
impl<T> Default for AtomicPtr<T> {
    /// Creates a null `AtomicPtr<T>`.
    #[inline]
    fn default() -> Self {
        Self::new(core::ptr::null_mut())
    }
}

#[cfg(polyfill_ptr)]
impl<T> From<*mut T> for AtomicPtr<T> {
    #[inline]
    fn from(v: *mut T) -> Self {
        Self::new(v)
    }
}

#[cfg(polyfill_ptr)]
impl<T> core::fmt::Debug for AtomicPtr<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.load(Ordering::SeqCst), f)
    }
}

#[cfg(polyfill_ptr)]
impl<T> core::fmt::Pointer for AtomicPtr<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Pointer::fmt(&self.load(Ordering::SeqCst), f)
    }
}

#[cfg(polyfill_ptr)]
unsafe impl<T> Sync for AtomicPtr<T> {}
#[cfg(polyfill_ptr)]
unsafe impl<T> Send for AtomicPtr<T> {}
#[cfg(polyfill_ptr)]
impl<T> core::panic::RefUnwindSafe for AtomicPtr<T> {}

#[cfg(polyfill_ptr)]
impl<T> AtomicPtr<T> {
    pub const fn new(v: *mut T) -> AtomicPtr<T> {
        Self {
            inner: core::cell::UnsafeCell::new(v),
        }
    }

    pub fn into_inner(self) -> *mut T {
        self.inner.into_inner()
    }

    pub fn get_mut(&mut self) -> &mut *mut T {
        self.inner.get_mut()
    }

    pub fn load(&self, _order: Ordering) -> *mut T {
        critical_section::with(|_| unsafe { *self.inner.get() })
    }

    pub fn store(&self, val: *mut T, _order: Ordering) {
        critical_section::with(|_| unsafe { *self.inner.get() = val });
    }

    pub fn swap(&self, val: *mut T, order: Ordering) -> *mut T {
        self.op(order, |_| val)
    }

    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        self.compare_exchange_weak(current, new, success, failure)
    }

    pub fn compare_exchange_weak(
        &self,
        current: *mut T,
        new: *mut T,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            if old == current {
                *val = new;
                Ok(old)
            } else {
                Err(old)
            }
        })
    }

    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<*mut T, *mut T>
    where
        F: FnMut(*mut T) -> Option<*mut T>,
    {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            if let Some(new) = f(old) {
                *val = new;
                Ok(old)
            } else {
                Err(old)
            }
        })
    }

    fn op(&self, _order: Ordering, f: impl FnOnce(*mut T) -> *mut T) -> *mut T {
        critical_section::with(|_| {
            let val = unsafe { &mut *self.inner.get() };
            let old = *val;
            *val = f(old);
            old
        })
    }
}
