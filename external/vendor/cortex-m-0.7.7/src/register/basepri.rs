//! Base Priority Mask Register

/// Reads the CPU register
#[inline]
pub fn read() -> u8 {
    call_asm!(__basepri_r() -> u8)
}

/// Writes to the CPU register
///
/// **IMPORTANT** If you are using a Cortex-M7 device with revision r0p1 you MUST enable the
/// `cm7-r0p1` Cargo feature or this function WILL misbehave.
#[inline]
pub unsafe fn write(basepri: u8) {
    #[cfg(feature = "cm7-r0p1")]
    {
        call_asm!(__basepri_w_cm7_r0p1(basepri: u8));
    }

    #[cfg(not(feature = "cm7-r0p1"))]
    {
        call_asm!(__basepri_w(basepri: u8));
    }
}
