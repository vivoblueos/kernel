//! Base Priority Mask Register (conditional write)

/// Writes to BASEPRI *if*
///
/// - `basepri != 0` AND `basepri::read() == 0`, OR
/// - `basepri != 0` AND `basepri < basepri::read()`
///
/// **IMPORTANT** If you are using a Cortex-M7 device with revision r0p1 you MUST enable the
/// `cm7-r0p1` Cargo feature or this function WILL misbehave.
#[inline]
pub fn write(basepri: u8) {
    #[cfg(feature = "cm7-r0p1")]
    {
        call_asm!(__basepri_max_cm7_r0p1(basepri: u8));
    }

    #[cfg(not(feature = "cm7-r0p1"))]
    {
        call_asm!(__basepri_max(basepri: u8));
    }
}
