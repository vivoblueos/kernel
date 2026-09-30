// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2022-2023 Amazon.com, Inc. or its affiliates.
//
// Author(s):
//   - Ali Saidi <alisaidi@amazon.com>

#[cfg(target_arch = "aarch64")]
use core::arch::asm;

/// Implement an interface for accessing Arm v8.5 RNG instructions.
///
/// An empty struct is used to confirm that the system has the instructions available.
///
/// # Example
///
/// ```no_run
/// use aarch64_cpu::asm::random::ArmRng;
/// if let Some(rng) = ArmRng::new() {
///     let rand_num = rng.rndr();
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub struct ArmRng;

impl ArmRng {
    /// Return an empty object that is used to gate calling rndr and rndrss on discovery of the
    /// feature so each call doesn't need to confirm it.
    #[cfg(target_arch = "aarch64")]
    #[inline]
    pub fn new() -> Option<Self> {
        use crate::registers::ID_AA64ISAR0_EL1;
        use tock_registers::interfaces::Readable;

        if ID_AA64ISAR0_EL1.is_set(ID_AA64ISAR0_EL1::RNDR) {
            Some(ArmRng)
        } else {
            None
        }
    }

    #[cfg(not(target_arch = "aarch64"))]
    pub fn new() -> Option<Self> {
        None
    }

    /// Return an random number from the Arm v8.5 RNG.
    ///
    /// This returns an option because the instruction can fail (e.g. the entropy is exhausted or
    /// the RNG has failed.)
    #[cfg(target_arch = "aarch64")]
    #[inline]
    pub fn rndr(&self) -> Option<u64> {
        let mut flags: u64;
        let mut data: u64;

        unsafe {
            asm!(
                "mrs {o}, s3_3_c2_c4_0",
                "mrs {f}, nzcv",
                o = out(reg) data,
                f = out(reg) flags,
                options(nomem, nostack));
        }

        if flags != 0 {
            None
        } else {
            Some(data)
        }
    }

    #[cfg(not(target_arch = "aarch64"))]
    pub fn rndr(&self) -> Option<u64> {
        None
    }

    /// Return a random number from the Arm v8.5 RNG after reseeding it.
    ///
    /// This returns an option because the instruction can fail (e.g. the entropy is exhausted or
    /// the RNG has failed.)
    #[cfg(target_arch = "aarch64")]
    #[inline]
    pub fn rndrss(&self) -> Option<u64> {
        let mut flags: u64;
        let mut data: u64;

        unsafe {
            asm!(
                "mrs {o}, s3_3_c2_c4_1",
                "mrs {f}, nzcv",
                o = out(reg) data,
                f = out(reg) flags,
                options(nomem, nostack));
        }

        if flags != 0 {
            None
        } else {
            Some(data)
        }
    }

    #[cfg(not(target_arch = "aarch64"))]
    pub fn rndrss(&self) -> Option<u64> {
        None
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;

    #[test]
    pub fn test_rndr() {
        // This works on Linux from userspace since Linux emulatates the Arm ID registers on the
        // userspace undef.
        if let Some(rand) = ArmRng::new() {
            assert!(rand.rndr().unwrap() != 0);
            assert!(rand.rndrss().unwrap() != 0);
        }
    }
}
