use quickcheck_macros::quickcheck;
use std::{fmt, prelude::v1::*};

use super::*;
use crate::{
    tests::ShadowAllocator,
    utils::{nonnull_slice_end, nonnull_slice_len},
};

trait TestFlexSource: FlexSource {
    type Options: quickcheck::Arbitrary;

    fn new(options: Self::Options) -> Self;
}

impl<T: core::alloc::GlobalAlloc + Default, const ALIGN: usize> TestFlexSource
    for GlobalAllocAsFlexSource<T, ALIGN>
{
    type Options = ();

    fn new((): ()) -> Self {
        Self(T::default())
    }
}

#[derive(Debug)]
struct TrackingFlexSource<T: FlexSource> {
    sa: ShadowAllocator,
    inner: T,
}

impl<T: TestFlexSource> TestFlexSource for TrackingFlexSource<T> {
    type Options = T::Options;

    fn new(options: T::Options) -> Self {
        Self {
            sa: ShadowAllocator::default(),
            inner: T::new(options),
        }
    }
}

impl<T: FlexSource> Drop for TrackingFlexSource<T> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            return;
        }

        if self.inner.supports_dealloc() {
            // All existing pools should have been removed by `FlexTlsf::drop`
            self.sa.assert_no_pools();
        }
    }
}

unsafe impl<T: FlexSource> FlexSource for TrackingFlexSource<T> {
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        log::trace!("FlexSource::alloc({:?})", min_size);
        let range = self.inner.alloc(min_size)?;
        log::trace!(" FlexSource::alloc(...) = {:?}", range);
        self.sa.insert_free_block(range.as_ptr());
        Some(range)
    }

    unsafe fn realloc_inplace_grow(
        &mut self,
        ptr: NonNull<[u8]>,
        min_new_len: usize,
    ) -> Option<usize> {
        log::trace!("FlexSource::realloc_inplace_grow{:?}", (ptr, min_new_len));
        let new_len = self.inner.realloc_inplace_grow(ptr, min_new_len)?;
        log::trace!(" FlexSource::realloc_inplace_grow(...) = {:?}", new_len);
        self.sa.append_free_block(std::ptr::slice_from_raw_parts(
            nonnull_slice_end(ptr),
            new_len - nonnull_slice_len(ptr),
        ));
        Some(new_len)
    }

    #[inline]
    fn min_align(&self) -> usize {
        self.inner.min_align()
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<[u8]>) {
        // TODO: check that `ptr` represents an exact allocation, not just
        //       a part of it
        self.sa.remove_pool(ptr.as_ptr());
        self.inner.dealloc(ptr);
        log::trace!("FlexSource::dealloc({:?})", ptr);
    }

    #[inline]
    fn is_contiguous_growable(&self) -> bool {
        self.inner.is_contiguous_growable()
    }

    #[inline]
    fn supports_dealloc(&self) -> bool {
        self.inner.supports_dealloc()
    }

    #[inline]
    fn supports_realloc_inplace_grow(&self) -> bool {
        self.inner.supports_realloc_inplace_grow()
    }
}

/// Continuous-growing flex source
struct CgFlexSource {
    pool: Vec<u8>,
    allocated: usize,
}

impl fmt::Debug for CgFlexSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CgFlexSource")
            .field("allocated", &self.allocated)
            .finish()
    }
}

impl TestFlexSource for CgFlexSource {
    type Options = u8;

    fn new(offset: u8) -> Self {
        Self {
            pool: std::vec![0u8; 1024 * 32],
            allocated: offset as usize,
        }
    }
}

unsafe impl FlexSource for CgFlexSource {
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        let allocated = self.allocated;
        let new_allocated = allocated
            .checked_add(min_size)
            .filter(|&x| x <= self.pool.len())?;

        self.allocated = new_allocated;

        // Slice the allocated of `self.pool`.
        //
        // - Do not do `&mut self.pool[..]` because mutably borrowing the whole
        //   `*self.pool` would invalidate the borrows made by previous
        //   allocations.
        //
        // - Do not create a mutable reference even to the sliced out part
        //   because the resulting pointer could not be expanded by
        //   `realloc_inplace_grow`.
        let pool_ptr = self.pool.as_mut_ptr();
        Some(crate::utils::nonnull_slice_from_raw_parts(
            NonNull::new(pool_ptr.add(allocated)).unwrap(),
            new_allocated - allocated,
        ))
    }

    unsafe fn realloc_inplace_grow(
        &mut self,
        ptr: NonNull<[u8]>,
        min_new_len: usize,
    ) -> Option<usize> {
        self.alloc(min_new_len - nonnull_slice_len(ptr))
            .map(|s| nonnull_slice_len(s) + nonnull_slice_len(ptr))
    }

    fn is_contiguous_growable(&self) -> bool {
        true
    }

    fn supports_realloc_inplace_grow(&self) -> bool {
        true
    }

    fn min_align(&self) -> usize {
        1
    }
}

fn fill_data(p: NonNull<[u8]>) {
    use std::mem::MaybeUninit;
    let slice = unsafe { &mut *(p.as_ptr() as *mut [MaybeUninit<u8>]) };
    for (i, p) in slice.iter_mut().enumerate() {
        *p = MaybeUninit::new((i as u8).reverse_bits());
    }
}

fn verify_data(p: NonNull<[u8]>) {
    let slice = unsafe { p.as_ref() };
    for (i, p) in slice.iter().enumerate() {
        assert_eq!(*p, (i as u8).reverse_bits());
    }
}

macro_rules! gen_test {
    ($mod:ident, $source:ty, $($tt:tt)*) => {
        mod $mod {
            use super::*;
            type TheTlsf = FlexTlsf<TrackingFlexSource<$source>, $($tt)*>;

            #[quickcheck]
            fn minimal(source_options: <$source as TestFlexSource>::Options) {
                let _ = env_logger::builder().is_test(true).try_init();

                let mut tlsf = TheTlsf::new(TrackingFlexSource::new(source_options));

                log::trace!("tlsf = {:?}", tlsf);

                let ptr = tlsf.allocate(Layout::from_size_align(1, 1).unwrap());
                log::trace!("ptr = {:?}", ptr);
                if let Some(ptr) = ptr {
                    unsafe { tlsf.deallocate(ptr, 1) };
                }
            }

            #[quickcheck]
            fn aadaadaraaadr(source_options: <$source as TestFlexSource>::Options) {
                let _ = env_logger::builder().is_test(true).try_init();

                let mut tlsf = TheTlsf::new(TrackingFlexSource::new(source_options));

                log::trace!("tlsf = {:?}", tlsf);

                let ptr1 = tlsf.allocate(Layout::from_size_align(20, 16).unwrap());
                log::trace!("ptr1 = {:?}", ptr1);
                let ptr2 = tlsf.allocate(Layout::from_size_align(21, 1).unwrap());
                log::trace!("ptr2 = {:?}", ptr2);
                if let Some(ptr1) = ptr1 {
                    unsafe { tlsf.deallocate(ptr1, 16) };
                }
                let ptr3 = tlsf.allocate(Layout::from_size_align(0, 32).unwrap());
                log::trace!("ptr3 = {:?}", ptr3);
                let ptr4 = tlsf.allocate(Layout::from_size_align(10, 8).unwrap());
                log::trace!("ptr4 = {:?}", ptr4);
                if let Some(ptr2) = ptr2 {
                    unsafe { tlsf.deallocate(ptr2, 1) };
                    log::trace!("deallocate(ptr2)");
                }
                let ptr5 = tlsf.allocate(Layout::from_size_align(12, 8).unwrap());
                log::trace!("ptr5 = {:?}", ptr5);
                let ptr3 = ptr3.and_then(|ptr3| unsafe {
                    tlsf.reallocate(ptr3, Layout::from_size_align(0, 32).unwrap())
                });
                log::trace!("ptr3 = {:?}", ptr3);
                let ptr6 = tlsf.allocate(Layout::from_size_align(24, 2).unwrap());
                log::trace!("ptr6 = {:?}", ptr6);
                let ptr7 = tlsf.allocate(Layout::from_size_align(11, 16).unwrap());
                log::trace!("ptr7 = {:?}", ptr7);
                let ptr8 = tlsf.allocate(Layout::from_size_align(1, 32).unwrap());
                log::trace!("ptr8 = {:?}", ptr8);
                if let Some(ptr5) = ptr5 {
                    unsafe { tlsf.deallocate(ptr5, 8) };
                    log::trace!("deallocate(ptr5)");
                }
                let ptr3 = ptr3.and_then(|ptr3| unsafe {
                    tlsf.reallocate(ptr3, Layout::from_size_align(4, 32).unwrap())
                });
                log::trace!("ptr3 = {:?}", ptr3);
            }

            #[quickcheck]
            fn random(source_options: <$source as TestFlexSource>::Options, max_alloc_size: usize, bytecode: Vec<u8>) {
                random_inner(source_options, max_alloc_size, bytecode);
            }

            fn random_inner(source_options: <$source as TestFlexSource>::Options, max_alloc_size: usize, bytecode: Vec<u8>) -> Option<()> {
                let max_alloc_size = max_alloc_size % 0x10000;

                let mut tlsf = TheTlsf::new(TrackingFlexSource::new(source_options));
                macro_rules! sa {
                    () => {
                        unsafe { tlsf.source_mut_unchecked() }.sa
                    };
                }

                log::trace!("tlsf = {:?}", tlsf);

                #[derive(Debug)]
                struct Alloc {
                    ptr: NonNull<u8>,
                    layout: Layout,
                }
                let mut allocs = Vec::new();

                let mut it = bytecode.iter().cloned();
                loop {
                    match it.next()? % 8 {
                        0..=2 => {
                            let len = u32::from_le_bytes([
                                it.next()?,
                                it.next()?,
                                it.next()?,
                                0,
                            ]);
                            let len = ((len as u64 * max_alloc_size as u64) >> 24) as usize;
                            let align = 1 << (it.next()? % 6);
                            let layout = Layout::from_size_align(len, align).unwrap();
                            log::trace!("alloc {:?}", layout);

                            let ptr = tlsf.allocate(layout);
                            log::trace!(" → {:?}", ptr);

                            if let Some(ptr) = ptr {
                                allocs.push(Alloc { ptr, layout });
                                sa!().allocate(layout, ptr);

                                // Fill it with dummy data
                                fill_data(crate::utils::nonnull_slice_from_raw_parts(ptr, len));
                            }
                        }
                        3..=5 => {
                            let alloc_i = it.next()?;
                            if allocs.len() > 0 {
                                let alloc = allocs.swap_remove(alloc_i as usize % allocs.len());
                                log::trace!("dealloc {:?}", alloc);

                                // Make sure the stored dummy data is not corrupted
                                verify_data(crate::utils::nonnull_slice_from_raw_parts(alloc.ptr, alloc.layout.size()));

                                unsafe { tlsf.deallocate(alloc.ptr, alloc.layout.align()) };
                                sa!().deallocate(alloc.layout, alloc.ptr);
                            }
                        }
                        6..=7 => {
                            let alloc_i = it.next()?;
                            if allocs.len() > 0 {
                                let len = u32::from_le_bytes([
                                    it.next()?,
                                    it.next()?,
                                    it.next()?,
                                    0,
                                ]);
                                let len = ((len as u64 * max_alloc_size as u64) >> 24) as usize;

                                let alloc_i = alloc_i as usize % allocs.len();
                                let alloc = &mut allocs[alloc_i];
                                log::trace!("realloc {:?} to {:?}", alloc, len);

                                let new_layout = Layout::from_size_align(len, alloc.layout.align()).unwrap();

                                if let Some(ptr) = unsafe { tlsf.reallocate(alloc.ptr, new_layout) } {
                                    log::trace!(" {:?} → {:?}", alloc.ptr, ptr);

                                    // Check and refill the dummy data
                                    verify_data(crate::utils::nonnull_slice_from_raw_parts(ptr, len.min(alloc.layout.size())));
                                    fill_data(crate::utils::nonnull_slice_from_raw_parts(ptr, len));

                                    sa!().deallocate(alloc.layout, alloc.ptr);
                                    alloc.ptr = ptr;
                                    alloc.layout = new_layout;
                                    sa!().allocate(alloc.layout, alloc.ptr);
                                } else {
                                    log::trace!(" {:?} → fail", alloc.ptr);

                                }
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    };
}

type SysSource = GlobalAllocAsFlexSource<std::alloc::System, 1024>;
gen_test!(tlsf_sys_u8_u8_1_1, SysSource, u8, u8, 1, 1);
gen_test!(tlsf_sys_u8_u8_1_2, SysSource, u8, u8, 1, 2);
gen_test!(tlsf_sys_u8_u8_1_4, SysSource, u8, u8, 1, 4);
gen_test!(tlsf_sys_u8_u8_1_8, SysSource, u8, u8, 1, 8);
gen_test!(tlsf_sys_u8_u8_3_4, SysSource, u8, u8, 3, 4);
gen_test!(tlsf_sys_u8_u8_5_4, SysSource, u8, u8, 5, 4);
gen_test!(tlsf_sys_u8_u8_8_1, SysSource, u8, u8, 8, 1);
gen_test!(tlsf_sys_u8_u8_8_8, SysSource, u8, u8, 8, 8);
gen_test!(tlsf_sys_u16_u8_3_4, SysSource, u16, u8, 3, 4);
gen_test!(tlsf_sys_u16_u8_11_4, SysSource, u16, u8, 11, 4);
gen_test!(tlsf_sys_u16_u8_16_4, SysSource, u16, u8, 16, 4);
gen_test!(tlsf_sys_u16_u16_3_16, SysSource, u16, u16, 3, 16);
gen_test!(tlsf_sys_u16_u16_11_16, SysSource, u16, u16, 11, 16);
gen_test!(tlsf_sys_u16_u16_16_16, SysSource, u16, u16, 16, 16);
gen_test!(tlsf_sys_u16_u32_3_16, SysSource, u16, u32, 3, 16);
gen_test!(tlsf_sys_u16_u32_11_16, SysSource, u16, u32, 11, 16);
gen_test!(tlsf_sys_u16_u32_16_16, SysSource, u16, u32, 16, 16);
gen_test!(tlsf_sys_u16_u32_3_32, SysSource, u16, u32, 3, 32);
gen_test!(tlsf_sys_u16_u32_11_32, SysSource, u16, u32, 11, 32);
gen_test!(tlsf_sys_u16_u32_16_32, SysSource, u16, u32, 16, 32);
gen_test!(tlsf_sys_u32_u32_20_32, SysSource, u32, u32, 20, 32);
gen_test!(tlsf_sys_u32_u32_27_32, SysSource, u32, u32, 27, 32);
gen_test!(tlsf_sys_u32_u32_28_32, SysSource, u32, u32, 28, 32);
gen_test!(tlsf_sys_u32_u32_29_32, SysSource, u32, u32, 29, 32);
gen_test!(tlsf_sys_u32_u32_32_32, SysSource, u32, u32, 32, 32);
gen_test!(tlsf_sys_u64_u8_58_8, SysSource, u64, u64, 58, 8);
gen_test!(tlsf_sys_u64_u8_59_8, SysSource, u64, u64, 59, 8);
gen_test!(tlsf_sys_u64_u8_60_8, SysSource, u64, u64, 60, 8);
gen_test!(tlsf_sys_u64_u8_61_8, SysSource, u64, u64, 61, 8);
gen_test!(tlsf_sys_u64_u8_64_8, SysSource, u64, u64, 64, 8);

gen_test!(tlsf_cg_u8_u8_1_1, CgFlexSource, u8, u8, 1, 1);
gen_test!(tlsf_cg_u8_u8_1_2, CgFlexSource, u8, u8, 1, 2);
gen_test!(tlsf_cg_u8_u8_1_4, CgFlexSource, u8, u8, 1, 4);
gen_test!(tlsf_cg_u8_u8_1_8, CgFlexSource, u8, u8, 1, 8);
gen_test!(tlsf_cg_u8_u8_3_4, CgFlexSource, u8, u8, 3, 4);
gen_test!(tlsf_cg_u8_u8_5_4, CgFlexSource, u8, u8, 5, 4);
gen_test!(tlsf_cg_u8_u8_8_1, CgFlexSource, u8, u8, 8, 1);
gen_test!(tlsf_cg_u8_u8_8_8, CgFlexSource, u8, u8, 8, 8);
gen_test!(tlsf_cg_u16_u8_3_4, CgFlexSource, u16, u8, 3, 4);
gen_test!(tlsf_cg_u16_u8_11_4, CgFlexSource, u16, u8, 11, 4);
gen_test!(tlsf_cg_u16_u8_16_4, CgFlexSource, u16, u8, 16, 4);
gen_test!(tlsf_cg_u16_u16_3_16, CgFlexSource, u16, u16, 3, 16);
gen_test!(tlsf_cg_u16_u16_11_16, CgFlexSource, u16, u16, 11, 16);
gen_test!(tlsf_cg_u16_u16_16_16, CgFlexSource, u16, u16, 16, 16);
gen_test!(tlsf_cg_u16_u32_3_16, CgFlexSource, u16, u32, 3, 16);
gen_test!(tlsf_cg_u16_u32_11_16, CgFlexSource, u16, u32, 11, 16);
gen_test!(tlsf_cg_u16_u32_16_16, CgFlexSource, u16, u32, 16, 16);
gen_test!(tlsf_cg_u16_u32_3_32, CgFlexSource, u16, u32, 3, 32);
gen_test!(tlsf_cg_u16_u32_11_32, CgFlexSource, u16, u32, 11, 32);
gen_test!(tlsf_cg_u16_u32_16_32, CgFlexSource, u16, u32, 16, 32);
gen_test!(tlsf_cg_u32_u32_20_32, CgFlexSource, u32, u32, 20, 32);
gen_test!(tlsf_cg_u32_u32_27_32, CgFlexSource, u32, u32, 27, 32);
gen_test!(tlsf_cg_u32_u32_28_32, CgFlexSource, u32, u32, 28, 32);
gen_test!(tlsf_cg_u32_u32_29_32, CgFlexSource, u32, u32, 29, 32);
gen_test!(tlsf_cg_u32_u32_32_32, CgFlexSource, u32, u32, 32, 32);
gen_test!(tlsf_cg_u64_u8_58_8, CgFlexSource, u64, u64, 58, 8);
gen_test!(tlsf_cg_u64_u8_59_8, CgFlexSource, u64, u64, 59, 8);
gen_test!(tlsf_cg_u64_u8_60_8, CgFlexSource, u64, u64, 60, 8);
gen_test!(tlsf_cg_u64_u8_61_8, CgFlexSource, u64, u64, 61, 8);
gen_test!(tlsf_cg_u64_u8_64_8, CgFlexSource, u64, u64, 64, 8);
