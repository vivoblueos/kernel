//! Square root approximation function for a single-precision float.
//!
//! Method described at: <https://bits.stephan-brumme.com/squareRoot.html>

use super::F32;

impl F32 {
    /// Approximates the square root of a number with an average deviation of ~5%.
    ///
    /// Returns [`Self::NAN`] if `self` is a negative number.
    pub fn sqrt(self) -> Self {
        if self >= Self::ZERO {
            Self::from_bits((self.to_bits() + 0x3f80_0000) >> 1)
        } else {
            Self::NAN
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::F32;

    /// Deviation from the actual value (5%)
    pub(crate) const MAX_ERROR: f32 = 0.05;

    /// Square root test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS: &[(f32, f32)] = &[
        (1.0, 1.0),
        (2.0, 1.414),
        (3.0, 1.732),
        (4.0, 2.0),
        (5.0, 2.236),
        (10.0, 3.162),
        (100.0, 10.0),
        (250.0, 15.811),
        (500.0, 22.36),
        (1000.0, 31.622),
        (2500.0, 50.0),
        (5000.0, 70.710),
        (1000000.0, 1000.0),
        (2500000.0, 1581.138),
        (5000000.0, 2236.067),
        (10000000.0, 3162.277),
        (25000000.0, 5000.0),
        (50000000.0, 7071.067),
        (100000000.0, 10000.0),
    ];

    #[test]
    fn sanity_check() {
        for &(x, expected) in TEST_VECTORS {
            let sqrt_x = F32(x).sqrt();
            let allowed_delta = x * MAX_ERROR;
            let actual_delta = sqrt_x - expected;

            assert!(
                actual_delta <= allowed_delta,
                "delta {} too large: {} vs {}",
                actual_delta,
                sqrt_x,
                expected
            );
        }
    }

    #[test]
    fn negative_is_nan() {
        assert!(F32(-1.0).sqrt().is_nan());
    }
}
