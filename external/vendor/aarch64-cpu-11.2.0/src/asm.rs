// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Jorge Aparicio
//   - Andre Richter <andre.o.richter@gmail.com>

//! Wrappers around ARMv8-A instructions.

pub mod barrier;
pub mod random;

/// The classic no-op
#[inline(always)]
pub fn nop() {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("nop", options(nomem, nostack))
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Wait For Interrupt
///
/// For more details on wfi, refer to [here](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0802a/CIHEGBBF.html).
#[inline(always)]
pub fn wfi() {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("wfi", options(nomem, nostack))
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Wait For Event
///
/// For more details of wfe - sev pair, refer to [here](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0802a/CIHEGBBF.html).
#[inline(always)]
pub fn wfe() {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("wfe", options(nomem, nostack))
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Send EVent.Locally
///
/// SEV causes an event to be signaled to the local core within a multiprocessor system.
///
/// For more details of wfe - sev/sevl pair, refer to [here](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0802a/CIHEGBBF.html).
#[inline(always)]
pub fn sevl() {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("sevl", options(nomem, nostack))
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Send EVent.
///
/// SEV causes an event to be signaled to all cores within a multiprocessor system.
///
/// For more details of wfe - sev pair, refer to [here](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0802a/CIHEGBBF.html).
#[inline(always)]
pub fn sev() {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("sev", options(nomem, nostack))
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Exception return
///
/// Will jump to wherever the corresponding link register points to, and therefore never return.
#[inline(always)]
pub fn eret() -> ! {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("eret", options(nomem, nostack));
        core::hint::unreachable_unchecked()
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}

/// Function return
///
/// Will jump to wherever the corresponding link register points to, and therefore never return.
#[inline(always)]
pub fn ret() -> ! {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        core::arch::asm!("ret", options(nomem, nostack));
        core::hint::unreachable_unchecked()
    }

    #[cfg(not(target_arch = "aarch64"))]
    unimplemented!()
}
