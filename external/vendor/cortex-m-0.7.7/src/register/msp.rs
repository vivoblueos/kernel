//! Main Stack Pointer

/// Reads the CPU register
#[inline]
pub fn read() -> u32 {
    call_asm!(__msp_r() -> u32)
}

/// Writes `bits` to the CPU register
#[inline]
#[deprecated = "calling this function invokes Undefined Behavior, consider asm::bootstrap as an alternative"]
pub unsafe fn write(bits: u32) {
    call_asm!(__msp_w(bits: u32));
}

/// Reads the Non-Secure CPU register from Secure state.
///
/// Executing this function in Non-Secure state will return zeroes.
#[cfg(armv8m)]
#[inline]
pub fn read_ns() -> u32 {
    call_asm!(__msp_ns_r() -> u32)
}

/// Writes `bits` to the Non-Secure CPU register from Secure state.
///
/// Executing this function in Non-Secure state will be ignored.
#[cfg(armv8m)]
#[inline]
pub unsafe fn write_ns(bits: u32) {
    call_asm!(__msp_ns_w(bits: u32));
}
