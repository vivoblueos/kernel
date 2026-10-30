use quickcheck_macros::quickcheck;
use std::{alloc::Layout, prelude::v1::*};

use super::*;
use crate::tests::ShadowAllocator;

#[derive(Debug)]
struct Alloc {
    ptr: NonNull<u8>,
    layout: Layout,
}

macro_rules! gen_test {
    ($mod:ident, $($tt:tt)*) => {
        mod $mod {
            use super::*;
            type TheTlsf = GlobalTlsf<$($tt)*>;

            #[quickcheck]
            fn calloc_random(bytecode: Vec<u8>) {
                let tlsf: TheTlsf = TheTlsf::DEFAULT;

                let mut allocs = Vec::new();
                calloc_random_inner(&tlsf, &mut allocs, bytecode);

                // Deallocate all remaining allocations
                for alloc in allocs.iter() {
                    unsafe { CAlloc::deallocate(&tlsf, alloc.ptr) };
                }
            }

            fn calloc_random_inner(tlsf: &TheTlsf, allocs: &mut Vec<Alloc>, bytecode: Vec<u8>) -> Option<()> {
                let mut sa = ShadowAllocator::new_filled_with_free();

                let mut it = bytecode.iter().cloned();
                loop {
                    match it.next()? % 8 {
                        0..=2 => {
                            if allocs.len() > 64 {
                                continue;
                            }
                            let len = u32::from_le_bytes([
                                it.next()?,
                                0,
                                0,
                                0,
                            ]) as usize;
                            let align = 1 << (it.next()? % 6);
                            let layout = Layout::from_size_align(len, align).unwrap();
                            log::trace!("alloc {:?}", layout);

                            let ptr = CAlloc::allocate(tlsf, layout);
                            log::trace!(" → {:?}", ptr);

                            if let Some(ptr) = ptr {
                                assert!(unsafe { CAlloc::allocation_usable_size(tlsf, ptr) } >= len);

                                allocs.push(Alloc { ptr, layout });
                                sa.allocate(layout, ptr);
                            }
                        }
                        3..=5 => {
                            let alloc_i = it.next()?;
                            if allocs.len() > 0 {
                                let alloc = allocs.swap_remove(alloc_i as usize % allocs.len());
                                log::trace!("dealloc {:?}", alloc);

                                unsafe { CAlloc::deallocate(tlsf, alloc.ptr) };
                                sa.deallocate(alloc.layout, alloc.ptr);
                            }
                        }
                        6..=7 => {
                            let alloc_i = it.next()?;
                            if allocs.len() > 0 {
                                let len = u32::from_le_bytes([
                                    it.next()?,
                                    0,
                                    0,
                                    0,
                                ]) as usize;
                                let align = 1 << (it.next()? % 6);

                                let alloc_i = alloc_i as usize % allocs.len();
                                let alloc = &mut allocs[alloc_i];

                                let new_layout = Layout::from_size_align(len, align).unwrap();
                                log::trace!("realloc {:?} to {:?}", alloc, new_layout);

                                if let Some(ptr) = unsafe { CAlloc::reallocate(tlsf, alloc.ptr, new_layout) } {
                                    log::trace!(" {:?} → {:?}", alloc.ptr, ptr);
                                    sa.deallocate(alloc.layout, alloc.ptr);
                                    alloc.ptr = ptr;
                                    alloc.layout = new_layout;
                                    sa.allocate(alloc.layout, alloc.ptr);
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

gen_test!(default_globaltlsf, ());
gen_test!(small_globaltlsf, SmallGlobalTlsfOptions);
