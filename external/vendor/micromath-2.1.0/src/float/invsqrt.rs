//! Inverse square root approximation function for a single-precision float.
//!
//! Method described at: <https://bits.stephan-brumme.com/invSquareRoot.html>

use super::F32;

impl F32 {
    /// Approximate inverse square root with an average deviation of ~5%.
    pub fn invsqrt(self) -> Self {
        Self::from_bits(0x5f37_5a86 - (self.to_bits() >> 1))
    }
}

#[cfg(test)]
mod tests {
    use super::F32;
    use crate::float::sqrt::tests::TEST_VECTORS;

    /// Deviation from the actual value (5%)
    const MAX_ERROR: f32 = 0.05;

    #[test]
    fn sanity_check() {
        for (x, expected) in TEST_VECTORS {
            // The tests vectors are for sqrt(x), so invert the expected value
            let expected = 1.0 / expected;

            let invsqrt_x = F32(*x).invsqrt().0;
            let allowed_delta = x * MAX_ERROR;
            let actual_delta = invsqrt_x - expected;

            assert!(
                actual_delta <= allowed_delta,
                "delta {} too large: {} vs {}",
                actual_delta,
                invsqrt_x,
                expected
            );
        }
    }
}
