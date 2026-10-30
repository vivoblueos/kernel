//! Autodetection for CPU intrinsics, with fallback to the "soft" backend when
//! they are unavailable.

use crate::{backend::soft, Key, Tag};
use core::mem::ManuallyDrop;
use universal_hash::{
    consts::U16,
    crypto_common::{BlockSizeUser, KeySizeUser},
    KeyInit, Reset, UniversalHash,
};

#[cfg(all(target_arch = "aarch64", polyval_armv8))]
use super::pmull as intrinsics;

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use super::clmul as intrinsics;

#[cfg(all(target_arch = "aarch64", polyval_armv8))]
cpufeatures::new!(mul_intrinsics, "aes"); // `aes` implies PMULL

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
cpufeatures::new!(mul_intrinsics, "pclmulqdq");

/// **POLYVAL**: GHASH-like universal hash over GF(2^128).
pub struct Polyval {
    inner: Inner,
    token: mul_intrinsics::InitToken,
}

union Inner {
    intrinsics: ManuallyDrop<intrinsics::Polyval>,
    soft: ManuallyDrop<soft::Polyval>,
}

impl KeySizeUser for Polyval {
    type KeySize = U16;
}

impl Polyval {
    /// Initialize POLYVAL with the given `H` field element and initial block
    pub fn new_with_init_block(h: &Key, init_block: u128) -> Self {
        let (token, has_intrinsics) = mul_intrinsics::init_get();

        let inner = if has_intrinsics {
            Inner {
                intrinsics: ManuallyDrop::new(intrinsics::Polyval::new_with_init_block(
                    h, init_block,
                )),
            }
        } else {
            Inner {
                soft: ManuallyDrop::new(soft::Polyval::new_with_init_block(h, init_block)),
            }
        };

        Self { inner, token }
    }
}

impl KeyInit for Polyval {
    /// Initialize POLYVAL with the given `H` field element
    fn new(h: &Key) -> Self {
        Self::new_with_init_block(h, 0)
    }
}

impl BlockSizeUser for Polyval {
    type BlockSize = U16;
}

impl UniversalHash for Polyval {
    fn update_with_backend(
        &mut self,
        f: impl universal_hash::UhfClosure<BlockSize = Self::BlockSize>,
    ) {
        unsafe {
            if self.token.get() {
                f.call(&mut *self.inner.intrinsics)
            } else {
                f.call(&mut *self.inner.soft)
            }
        }
    }

    /// Get POLYVAL result (i.e. computed `S` field element)
    fn finalize(self) -> Tag {
        unsafe {
            if self.token.get() {
                ManuallyDrop::into_inner(self.inner.intrinsics).finalize()
            } else {
                ManuallyDrop::into_inner(self.inner.soft).finalize()
            }
        }
    }
}

impl Clone for Polyval {
    fn clone(&self) -> Self {
        let inner = if self.token.get() {
            Inner {
                intrinsics: ManuallyDrop::new(unsafe { (*self.inner.intrinsics).clone() }),
            }
        } else {
            Inner {
                soft: ManuallyDrop::new(unsafe { (*self.inner.soft).clone() }),
            }
        };

        Self {
            inner,
            token: self.token,
        }
    }
}

impl Reset for Polyval {
    fn reset(&mut self) {
        if self.token.get() {
            unsafe { (*self.inner.intrinsics).reset() }
        } else {
            unsafe { (*self.inner.soft).reset() }
        }
    }
}
