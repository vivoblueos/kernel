//! arctangent approximation for a single-precision float.
//!
//! Method described at:
//! <https://ieeexplore.ieee.org/document/6375931>

use super::F32;
use core::f32::consts::FRAC_PI_2;

impl F32 {
    /// Approximates `atan(x)` approximation in radians with a maximum error of
    /// `0.002`.
    ///
    /// Returns [`Self::NAN`] if the number is [`Self::NAN`].
    pub fn atan(self) -> Self {
        FRAC_PI_2 * self.atan_norm()
    }

    /// Approximates `atan(x)` normalized to the `[−1,1]` range with a maximum
    /// error of `0.1620` degrees.
    pub fn atan_norm(self) -> Self {
        const SIGN_MASK: u32 = 0x8000_0000;
        const B: f32 = 0.596_227;

        // Extract the sign bit
        let ux_s = SIGN_MASK & self.to_bits();

        // Calculate the arctangent in the first quadrant
        let bx_a = (B * self).abs();
        let n = bx_a + self * self;
        let atan_1q = n / (1.0 + bx_a + n);

        // Restore the sign bit and convert to float
        Self::from_bits(ux_s | atan_1q.to_bits())
    }
}

#[cfg(test)]
mod tests {
    use super::F32;
    use core::f32::consts;

    /// 0.1620 degrees in radians
    const MAX_ERROR: f32 = 0.003;

    #[test]
    fn sanity_check() {
        // Arctangent test vectors - `(input, output)`
        let test_vectors: &[(f32, f32)] = &[
            (3.0_f32.sqrt() / 3.0, consts::FRAC_PI_6),
            (1.0, consts::FRAC_PI_4),
            (3.0_f32.sqrt(), consts::FRAC_PI_3),
            (-(3.0_f32.sqrt()) / 3.0, -consts::FRAC_PI_6),
            (-1.0, -consts::FRAC_PI_4),
            (-(3.0_f32.sqrt()), -consts::FRAC_PI_3),
        ];

        for &(x, expected) in test_vectors {
            let actual = F32(x).atan().0;
            let delta = actual - expected;

            assert!(
                delta <= MAX_ERROR,
                "delta {} too large: {} vs {}",
                delta,
                actual,
                expected
            );
        }
    }

    #[test]
    fn zero() {
        assert_eq!(F32::ZERO.atan(), F32::ZERO);
    }

    #[test]
    fn nan() {
        assert!(F32::NAN.atan().is_nan());
    }
}
