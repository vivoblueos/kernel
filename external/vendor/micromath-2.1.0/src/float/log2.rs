//! log base 2 approximation for a single-precision float.

use super::F32;
use core::f32::consts::LOG2_E;

impl F32 {
    /// Approximates the base 2 logarithm of the number.
    pub fn log2(self) -> Self {
        self.ln() * LOG2_E
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    pub(crate) const MAX_ERROR: f32 = 0.001;

    /// log2(x) test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS: &[(f32, f32)] = &[
        (1e-20, -66.43856),
        (1e-19, -63.116634),
        (1e-18, -59.794704),
        (1e-17, -56.47278),
        (1e-16, -53.15085),
        (1e-15, -49.828922),
        (1e-14, -46.506992),
        (1e-13, -43.185066),
        (1e-12, -39.863136),
        (1e-11, -36.54121),
        (1e-10, -33.21928),
        (1e-09, -29.897352),
        (1e-08, -26.575424),
        (1e-07, -23.253496),
        (1e-06, -19.931568),
        (1e-05, -16.60964),
        (1e-04, -13.287712),
        (0.001, -9.965784),
        (0.01, -6.643856),
        (0.1, -3.321928),
        (10.0, 3.321928),
        (100.0, 6.643856),
        (1000.0, 9.965784),
        (10000.0, 13.287712),
        (100000.0, 16.60964),
        (1000000.0, 19.931568),
        (10000000.0, 23.253496),
        (100000000.0, 26.575424),
        (1000000000.0, 29.897352),
        (10000000000.0, 33.21928),
        (100000000000.0, 36.54121),
        (1000000000000.0, 39.863136),
        (10000000000000.0, 43.185066),
        (100000000000000.0, 46.506992),
        (1000000000000000.0, 49.828922),
        (1e+16, 53.15085),
        (1e+17, 56.47278),
        (1e+18, 59.794704),
        (1e+19, 63.116634),
    ];

    #[test]
    fn sanity_check() {
        assert_eq!(F32::ONE.log2(), F32::ZERO);

        for &(x, expected) in TEST_VECTORS {
            let ln_x = F32(x).log2().0;
            let relative_error = (ln_x - expected).abs() / expected;

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large: {} vs {}",
                relative_error,
                ln_x,
                expected
            );
        }
    }
}
