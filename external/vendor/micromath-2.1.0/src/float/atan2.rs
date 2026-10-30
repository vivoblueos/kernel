//! Four quadrant arctangent approximation for a single-precision float.
//!
//! Method described at: <https://ieeexplore.ieee.org/document/6375931>

use super::F32;
use core::f32::consts::PI;

impl F32 {
    /// Approximates the four quadrant arctangent of `self` (`y`) and
    /// `rhs` (`x`) in radians with a maximum error of `0.002`.
    ///
    /// - `x = 0`, `y = 0`: `0`
    /// - `x >= 0`: `arctan(y/x)` -> `[-pi/2, pi/2]`
    /// - `y >= 0`: `arctan(y/x) + pi` -> `(pi/2, pi]`
    /// - `y < 0`: `arctan(y/x) - pi` -> `(-pi, -pi/2)`
    pub fn atan2(self, rhs: Self) -> Self {
        let n = self.atan2_norm(rhs);
        PI / 2.0 * if n > 2.0 { n - 4.0 } else { n }
    }

    /// Approximates `atan2(y,x)` normalized to the `[0, 4)` range with a maximum
    /// error of `0.1620` degrees.
    pub(crate) fn atan2_norm(self, rhs: Self) -> Self {
        const SIGN_MASK: u32 = 0x8000_0000;
        const B: f32 = 0.596_227;

        let y = self;
        let x = rhs;

        // Extract sign bits from floating point values
        let ux_s = SIGN_MASK & x.to_bits();
        let uy_s = SIGN_MASK & y.to_bits();

        // Determine quadrant offset
        let q = ((!ux_s & uy_s) >> 29 | ux_s >> 30) as f32;

        // Calculate arctangent in the first quadrant
        let bxy_a = (B * x * y).abs();
        let n = bxy_a + y * y;
        let atan_1q = n / (x * x + bxy_a + n);

        // Translate it to the proper quadrant
        let uatan_2q = (ux_s ^ uy_s) | atan_1q.to_bits();
        Self(q) + Self::from_bits(uatan_2q)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;
    use core::f32::consts::PI;

    /// 0.1620 degrees in radians
    const MAX_ERROR: f32 = 0.003;

    #[test]
    fn sanity_check() {
        let test_vectors: &[(f32, f32, f32)] = &[
            (0.0, 1.0, 0.0),
            (0.0, -1.0, PI),
            (3.0, 2.0, (3.0f32 / 2.0).atan()),
            (2.0, -1.0, (2.0f32 / -1.0).atan() + PI),
            (-2.0, -1.0, (-2.0f32 / -1.0).atan() - PI),
        ];

        for &(y, x, expected) in test_vectors {
            let actual = F32(y).atan2(F32(x)).0;
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
}
