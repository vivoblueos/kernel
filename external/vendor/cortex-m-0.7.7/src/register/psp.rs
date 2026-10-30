//! Process Stack Pointer

/// Reads the CPU register
#[inline]
pub fn read() -> u32 {
    call_asm!(__psp_r() -> u32)
}

/// Writes `bits` to the CPU register
#[inline]
pub unsafe fn write(bits: u32) {
    call_asm!(__psp_w(bits: u32))
}
