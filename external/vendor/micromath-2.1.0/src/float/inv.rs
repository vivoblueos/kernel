//! Fast approximation of `1/x`.
//!
//! Method described at: <https://bits.stephan-brumme.com/inverse.html>

use super::F32;

impl F32 {
    /// Fast approximation of `1/x`.
    pub fn inv(self) -> Self {
        Self(f32::from_bits(0x7f00_0000 - self.0.to_bits()))
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::F32;

    /// Deviation from the actual value (8%)
    pub(crate) const MAX_ERROR: f32 = 0.08;

    #[test]
    fn sanity_check() {
        for x in 0..100 {
            let x = F32(x as f32);
            let inv_x = x.inv().0;
            let expected = 1.0 / x;
            let allowed_delta = x * MAX_ERROR;
            let actual_delta = inv_x - expected;

            assert!(
                actual_delta <= allowed_delta,
                "delta {} too large: {} vs {}",
                actual_delta,
                inv_x,
                expected
            );
        }
    }
}
