use const_default1::ConstDefault;
use core::{
    alloc,
    cell::UnsafeCell,
    marker::PhantomData,
    ops,
    ptr::{self, NonNull},
};

use super::FlexTlsf;

// `doc(cfg(...))` needs to be attached to the type for it to be displayed
// on the docs.
if_supported_target! {
    /// [`Tlsf`] as a global allocator.
    ///
    /// [`Tlsf`]: crate::Tlsf
    pub struct GlobalTlsf<Options: GlobalTlsfOptions = ()> {
        inner: UnsafeCell<TheTlsf<Options>>,
        #[cfg(not(doc))]
        mutex: os::Mutex,
        _phantom: PhantomData<fn() -> Options>,
    }
}

cfg_if::cfg_if! {
    if #[cfg(doc)] {
        // don't compile `os` in rustdoc
    } else if #[cfg(unix)] {
        mod unix;
        use self::unix as os;
    } else if #[cfg(target_arch = "wasm32")] {
        mod wasm32;
        use self::wasm32 as os;
    } else {
        compile_error!(
            "`crate::global` shouldn't be present when \
            compiling for an unsupported target"
        );
    }
}

#[cfg(doc)]
type TheTlsf<Options> = Options;
#[cfg(not(doc))]
type TheTlsf<Options> =
    FlexTlsf<os::Source<Options>, usize, usize, { usize::BITS as usize }, { usize::BITS as usize }>;

impl<Options: GlobalTlsfOptions> ConstDefault for GlobalTlsf<Options> {
    #[allow(clippy::declare_interior_mutable_const)]
    const DEFAULT: Self = Self::new();
}

if_supported_target! {
    /// The options for [`GlobalTlsf`].
    pub trait GlobalTlsfOptions {
        /// Enables the specialized reallocation routine. This option might
        /// improve the memory usage and runtime performance but increases the
        /// code size considerably.
        ///
        /// It's enabled by default.
        const ENABLE_REALLOCATION: bool = true;

        /// Instructs the allocator to coalesce consecutive system memory
        /// allocations into one large memory pool whenever possible.
        ///
        /// Warning: If you are going to create allocations larger than or
        /// roughly as large as the system page size, turning off this option
        /// can cause an excessive memory usage.
        ///
        /// It's enabled by default.
        const COALESCE_POOLS: bool = true;
    }
}

impl GlobalTlsfOptions for () {}

if_supported_target! {
    /// [`GlobalTlsfOptions`] with all options set to optimize for code size.
    #[derive(Debug)]
    pub struct SmallGlobalTlsfOptions;
}

if_supported_target! {
    /// An instantiation of [`GlobalTlsf`] optimized for code size.
    pub type SmallGlobalTlsf = GlobalTlsf<SmallGlobalTlsfOptions>;
}

impl GlobalTlsfOptions for SmallGlobalTlsfOptions {
    const ENABLE_REALLOCATION: bool = false;
    const COALESCE_POOLS: bool = false;
}

unsafe impl<Options: GlobalTlsfOptions> Send for GlobalTlsf<Options> {}
unsafe impl<Options: GlobalTlsfOptions> Sync for GlobalTlsf<Options> {}

impl<Options: GlobalTlsfOptions> GlobalTlsf<Options> {
    /// Construct an empty instance of `Self`.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: UnsafeCell::new(ConstDefault::DEFAULT),
            mutex: ConstDefault::DEFAULT,
            _phantom: PhantomData,
        }
    }
}

impl<Options: GlobalTlsfOptions> Default for GlobalTlsf<Options> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<Options: GlobalTlsfOptions> GlobalTlsf<Options> {
    #[inline]
    fn lock_inner(&self) -> impl ops::DerefMut<Target = TheTlsf<Options>> + '_ {
        struct LockGuard<'a, Options: GlobalTlsfOptions>(&'a GlobalTlsf<Options>);

        impl<Options: GlobalTlsfOptions> ops::Deref for LockGuard<'_, Options> {
            type Target = TheTlsf<Options>;

            #[inline]
            fn deref(&self) -> &Self::Target {
                // Safety: Protected by `mutex`
                unsafe { &*self.0.inner.get() }
            }
        }

        impl<Options: GlobalTlsfOptions> ops::DerefMut for LockGuard<'_, Options> {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                // Safety: Protected by `mutex`
                unsafe { &mut *self.0.inner.get() }
            }
        }

        impl<Options: GlobalTlsfOptions> Drop for LockGuard<'_, Options> {
            #[inline]
            fn drop(&mut self) {
                self.0.mutex.unlock();
            }
        }

        self.mutex.lock();
        LockGuard(self)
    }
}

unsafe impl<Options: GlobalTlsfOptions> alloc::GlobalAlloc for GlobalTlsf<Options> {
    #[inline]
    unsafe fn alloc(&self, layout: alloc::Layout) -> *mut u8 {
        let mut inner = self.lock_inner();
        inner
            .allocate(layout)
            .map(NonNull::as_ptr)
            .unwrap_or(ptr::null_mut())
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: alloc::Layout) {
        let mut inner = self.lock_inner();

        // [tag:global_dealloc_restore_provenance]
        //
        // <https://github.com/rust-lang/miri/issues/2104>
        // In current Miri with Stacked Borrows aliasing model, global heap
        // allocations lose the provenance for the memory outside `layout`,
        // which prevents us from accessing their allocation metadata and
        // adjacent memory blocks. To work around this, we restore the original
        // provenance from the containing memory pool.
        //
        // [ref:flex_force_pool_ftr_miri]
        // `restore_provenance` can be used here because `FlexTlsf::
        // growable_pool` is unconditionally enabled in `cfg(miri)`.
        #[cfg(miri)]
        let ptr = inner.restore_provenance(ptr);

        // Safety: All allocations are non-null
        let ptr = NonNull::new_unchecked(ptr);
        // Safety: `ptr` denotes a previous allocation with alignment
        //         `layout.align()`
        inner.deallocate(ptr, layout.align());
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: alloc::Layout, new_size: usize) -> *mut u8 {
        let mut inner = self.lock_inner();

        // See [ref:global_dealloc_restore_provenance]
        #[cfg(miri)]
        let ptr = inner.restore_provenance(ptr);

        // Safety: All allocations are non-null
        let ptr = NonNull::new_unchecked(ptr);
        // Safety: `layout.align()` is a power of two, and the size parameter's
        //         validity is upheld by the caller
        let new_layout = alloc::Layout::from_size_align_unchecked(new_size, layout.align());
        if Options::ENABLE_REALLOCATION {
            // Safety: `ptr` denotes a previous allocation with alignment
            //         `layout.align()`
            inner
                .reallocate(ptr, new_layout)
                .map(NonNull::as_ptr)
                .unwrap_or(ptr::null_mut())
        } else if let Some(new_ptr) = inner.allocate(new_layout) {
            // Safety: the previously allocated block cannot overlap the
            //         newly allocated block.
            //         The safety contract for `deallocate` must be upheld
            //         by the caller.
            ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), layout.size().min(new_size));
            inner.deallocate(ptr, layout.align());
            new_ptr.as_ptr()
        } else {
            ptr::null_mut()
        }
    }
}

/// Provides allocation functions modelled after the standard C and POSIX
/// allocation functions (e.g., `malloc`, `memalign`).
///
/// Note that this trait might require a less efficient implementation than
/// [`core::alloc::GlobalAlloc`]. This applies to [`GlobalTlsf`].
pub unsafe trait CAlloc {
    /// Allocate a memory block.
    ///
    /// Returns the starting address of the allocated memory block on success;
    /// `None` otherwise.
    fn allocate(&self, layout: alloc::Layout) -> Option<NonNull<u8>>;

    /// Deallocate a previously allocated memory block.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated by calling
    ///    [`Self::allocate`] on `self`.
    ///
    unsafe fn deallocate(&self, ptr: NonNull<u8>);

    /// Shrink or grow a previously allocated memory block.
    ///
    /// Returns the new starting address of the memory block on success;
    /// `None` otherwise.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated by calling
    ///    [`Self::allocate`] on `self`.
    ///
    unsafe fn reallocate(&self, ptr: NonNull<u8>, new_layout: alloc::Layout)
        -> Option<NonNull<u8>>;

    /// Get the actual usable size of a previously allocated memory block.
    ///
    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated by calling
    ///    [`Self::allocate`] on `self`.
    ///
    unsafe fn allocation_usable_size(&self, ptr: NonNull<u8>) -> usize;
}

unsafe impl<Options: GlobalTlsfOptions> CAlloc for GlobalTlsf<Options> {
    fn allocate(&self, layout: alloc::Layout) -> Option<NonNull<u8>> {
        let mut inner = self.lock_inner();
        inner.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>) {
        let mut inner = self.lock_inner();
        // Safety: `ptr` denotes a previous allocation
        inner.deallocate_unknown_align(ptr);
    }

    unsafe fn reallocate(
        &self,
        ptr: NonNull<u8>,
        new_layout: alloc::Layout,
    ) -> Option<NonNull<u8>> {
        let mut inner = self.lock_inner();
        if let Some(new_ptr) = inner.allocate(new_layout) {
            // Safety: `ptr` denotes a previous allocation
            let old_size = TheTlsf::<Options>::size_of_allocation_unknown_align(ptr);
            // Safety: the previously allocated block cannot overlap the
            //         newly allocated block.
            //         The safety contract for `deallocate` must be upheld
            //         by the caller.
            ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.as_ptr(),
                new_layout.size().min(old_size),
            );
            inner.deallocate_unknown_align(ptr);
            Some(new_ptr)
        } else {
            None
        }
    }

    unsafe fn allocation_usable_size(&self, ptr: NonNull<u8>) -> usize {
        // Safety: `ptr` denotes a previous allocation
        TheTlsf::<Options>::size_of_allocation_unknown_align(ptr)
    }
}

#[cfg(test)]
mod tests;
