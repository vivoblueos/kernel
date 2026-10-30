//! Cortex-M Security Extensions
//!
//! This module provides several helper functions to support Armv8-M and Armv8.1-M Security
//! Extensions.
//! Most of this implementation is directly inspired by the "Armv8-M Security Extensions:
//! Requirements on Development Tools" document available here:
//! https://developer.arm.com/docs/ecm0359818/latest
//!
//! Please note that the TT instructions support as described part 4 of the document linked above is
//! not part of CMSE but is still present in this module. The TT instructions return the
//! configuration of the Memory Protection Unit at an address.
//!
//! # Notes
//!
//! * Non-Secure Unprivileged code will always read zeroes from TestTarget and should not use it.
//! * Non-Secure Privileged code can check current (AccessType::Current) and Non-Secure Unprivileged
//!   accesses (AccessType::Unprivileged).
//! * Secure Unprivileged code can check Non-Secure Unprivileged accesses (AccessType::NonSecure).
//! * Secure Privileged code can check all access types.
//!
//! # Example
//!
//! ```
//! use cortex_m::cmse::{TestTarget, AccessType};
//!
//! // suspect_address was given by Non-Secure to a Secure function to write at it.
//! // But is it allowed to?
//! let suspect_address_test = TestTarget::check(0xDEADBEEF as *mut u32,
//!                                              AccessType::NonSecureUnprivileged);
//! if suspect_address_test.ns_read_and_writable() {
//!     // Non-Secure can not read or write this address!
//! }
//! ```

use crate::asm::{tt, tta, ttat, ttt};
use bitfield::bitfield;

/// Memory access behaviour: determine which privilege execution mode is used and which Memory
/// Protection Unit (MPU) is used.
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum AccessType {
    /// Access using current privilege level and reading from current security state MPU.
    /// Uses the TT instruction.
    Current,
    /// Unprivileged access reading from current security state MPU. Uses the TTT instruction.
    Unprivileged,
    /// Access using current privilege level reading from Non-Secure MPU. Uses the TTA instruction.
    /// Undefined if used from Non-Secure state.
    NonSecure,
    /// Unprivilege access reading from Non-Secure MPU. Uses the TTAT instruction.
    /// Undefined if used from Non-Secure state.
    NonSecureUnprivileged,
}

/// Abstraction of TT instructions and helper functions to determine the security and privilege
/// attribute of a target address, accessed in different ways.
#[derive(PartialEq, Copy, Clone, Debug)]
pub struct TestTarget {
    tt_resp: TtResp,
    access_type: AccessType,
}

bitfield! {
    /// Test Target Response Payload
    ///
    /// Provides the response payload from a TT, TTA, TTT or TTAT instruction.
    #[derive(PartialEq, Copy, Clone)]
    struct TtResp(u32);
    impl Debug;
    mregion, _: 7, 0;
    sregion, _: 15, 8;
    mrvalid, _: 16;
    srvalid, _: 17;
    r, _: 18;
    rw, _: 19;
    nsr, _: 20;
    nsrw, _: 21;
    s, _: 22;
    irvalid, _: 23;
    iregion, _: 31, 24;
}

impl TestTarget {
    /// Creates a Test Target Response Payload by testing addr using access_type.
    #[inline]
    pub fn check(addr: *mut u32, access_type: AccessType) -> Self {
        let tt_resp = match access_type {
            AccessType::Current => TtResp(tt(addr)),
            AccessType::Unprivileged => TtResp(ttt(addr)),
            AccessType::NonSecure => TtResp(tta(addr)),
            AccessType::NonSecureUnprivileged => TtResp(ttat(addr)),
        };

        TestTarget {
            tt_resp,
            access_type,
        }
    }

    /// Creates a Test Target Response Payload by testing the zone from addr to addr + size - 1
    /// using access_type.
    /// Returns None if:
    ///   * the address zone overlaps SAU, IDAU or MPU region boundaries
    ///   * size is 0
    ///   * addr + size - 1 overflows
    #[inline]
    pub fn check_range(addr: *mut u32, size: usize, access_type: AccessType) -> Option<Self> {
        let begin: usize = addr as usize;
        // Last address of the range (addr + size - 1). This also checks if size is 0.
        let end: usize = begin.checked_add(size.checked_sub(1)?)?;

        // Regions are aligned at 32-byte boundaries. If the address range fits in one 32-byte
        // address line, a single TT instruction suffices. This is the case when the following
        // constraint holds.
        let single_check: bool = (begin % 32).checked_add(size)? <= 32usize;

        let test_start = TestTarget::check(addr, access_type);

        if single_check {
            Some(test_start)
        } else {
            let test_end = TestTarget::check(end as *mut u32, access_type);
            // Check that the range does not cross SAU, IDAU or MPU region boundaries.
            if test_start != test_end {
                None
            } else {
                Some(test_start)
            }
        }
    }

    /// Access type that was used for this test target.
    #[inline]
    pub fn access_type(self) -> AccessType {
        self.access_type
    }

    /// Get the raw u32 value returned by the TT instruction used.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.tt_resp.0
    }

    /// Read accessibility of the target address. Only returns the MPU settings without checking
    /// the Security state of the target.
    /// For Unprivileged and NonSecureUnprivileged access types, returns the permissions for
    /// unprivileged access, regardless of whether the current mode is privileged or unprivileged.
    /// Returns false if the TT instruction was executed from an unprivileged mode
    /// and the NonSecure access type was not specified.
    /// Returns false if the address matches multiple MPU regions.
    #[inline]
    pub fn readable(self) -> bool {
        self.tt_resp.r()
    }

    /// Read and write accessibility of the target address. Only returns the MPU settings without
    /// checking the Security state of the target.
    /// For Unprivileged and NonSecureUnprivileged access types, returns the permissions for
    /// unprivileged access, regardless of whether the current mode is privileged or unprivileged.
    /// Returns false if the TT instruction was executed from an unprivileged mode
    /// and the NonSecure access type was not specified.
    /// Returns false if the address matches multiple MPU regions.
    #[inline]
    pub fn read_and_writable(self) -> bool {
        self.tt_resp.rw()
    }

    /// Indicate the MPU region number containing the target address.
    /// Returns None if the value is not valid:
    ///   * the MPU is not implemented or MPU_CTRL.ENABLE is set to zero
    ///   * the register argument specified by the MREGION field does not match any enabled MPU regions
    ///   * the address matched multiple MPU regions
    ///   * the address specified by the SREGION field is exempt from the secure memory attribution
    ///   * the TT instruction was executed from an unprivileged mode and the A flag was not specified.
    #[inline]
    pub fn mpu_region(self) -> Option<u8> {
        if self.tt_resp.srvalid() {
            // Cast is safe as SREGION field is defined on 8 bits.
            Some(self.tt_resp.sregion() as u8)
        } else {
            None
        }
    }

    /// Indicates the Security attribute of the target address. Independent of AccessType.
    /// Always zero when the test target is done in the Non-Secure state.
    #[inline]
    pub fn secure(self) -> bool {
        self.tt_resp.s()
    }

    /// Non-Secure Read accessibility of the target address.
    /// Same as readable() && !secure()
    #[inline]
    pub fn ns_readable(self) -> bool {
        self.tt_resp.nsr()
    }

    /// Non-Secure Read and Write accessibility of the target address.
    /// Same as read_and_writable() && !secure()
    #[inline]
    pub fn ns_read_and_writable(self) -> bool {
        self.tt_resp.nsrw()
    }

    /// Indicate the IDAU region number containing the target address. Independent of AccessType.
    /// Returns None if the value is not valid:
    ///   * the IDAU cannot provide a region number
    ///   * the address is exempt from security attribution
    ///   * the test target is done from Non-Secure state
    #[inline]
    pub fn idau_region(self) -> Option<u8> {
        if self.tt_resp.irvalid() {
            // Cast is safe as IREGION field is defined on 8 bits.
            Some(self.tt_resp.iregion() as u8)
        } else {
            None
        }
    }

    /// Indicate the SAU region number containing the target address. Independent of AccessType.
    /// Returns None if the value is not valid:
    ///   * SAU_CTRL.ENABLE is set to zero
    ///   * the register argument specified in the SREGION field does not match any enabled SAU regions
    ///   * the address specified matches multiple enabled SAU regions
    ///   * the address specified by the SREGION field is exempt from the secure memory attribution
    ///   * the TT instruction was executed from the Non-secure state or the Security Extension is not
    ///     implemented
    #[inline]
    pub fn sau_region(self) -> Option<u8> {
        if self.tt_resp.srvalid() {
            // Cast is safe as SREGION field is defined on 8 bits.
            Some(self.tt_resp.sregion() as u8)
        } else {
            None
        }
    }
}
