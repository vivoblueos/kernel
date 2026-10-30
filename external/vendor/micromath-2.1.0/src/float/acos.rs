//! arccos approximation for a single-precision float.
//!
//! Method described at:
//! <https://math.stackexchange.com/questions/2908908/express-arccos-in-terms-of-arctan>

use super::F32;
use core::f32::consts::PI;

impl F32 {
    /// Computes `acos(x)` approximation in radians in the range `[0, pi]`.
    pub(crate) fn acos(self) -> Self {
        if self > 0.0 {
            ((Self::ONE - self * self).sqrt() / self).atan()
        } else if self == 0.0 {
            Self(PI / 2.0)
        } else {
            ((Self::ONE - self * self).sqrt() / self).atan() + PI
        }
    }
}

#[cfg(test)]
mod tests {
    use super::F32;
    use core::f32::consts;

    const MAX_ERROR: f32 = 0.03;

    #[test]
    fn sanity_check() {
        // Arccosine test vectors - `(input, output)`
        let test_vectors: &[(f32, f32)] = &[
            (2.000, f32::NAN),
            (1.000, 0.0),
            (0.866, consts::FRAC_PI_6),
            (0.707, consts::FRAC_PI_4),
            (0.500, consts::FRAC_PI_3),
            (f32::EPSILON, consts::FRAC_PI_2),
            (0.000, consts::FRAC_PI_2),
            (-f32::EPSILON, consts::FRAC_PI_2),
            (-0.500, 2.0 * consts::FRAC_PI_3),
            (-0.707, 3.0 * consts::FRAC_PI_4),
            (-0.866, 5.0 * consts::FRAC_PI_6),
            (-1.000, consts::PI),
            (-2.000, f32::NAN),
        ];

        for &(x, expected) in test_vectors {
            let actual = F32(x).acos();
            if expected.is_nan() {
                assert!(
                    actual.is_nan(),
                    "acos({}) returned {}, should be NAN",
                    x,
                    actual
                );
            } else {
                let delta = (actual - expected).abs();

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
}
