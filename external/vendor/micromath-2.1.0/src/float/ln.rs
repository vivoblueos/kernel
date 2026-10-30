//! Natural log (ln) approximation for a single-precision float.
//!
//! Method described at: <https://stackoverflow.com/a/44232045/>
//!
//! Modified to not be restricted to int range and only values of x above 1.0.
//! Also got rid of most of the slow conversions. Should work for all positive values of x.

use super::{EXPONENT_MASK, F32};
use core::f32::consts::LN_2;

impl F32 {
    /// Approximates the natural logarithm of the number.
    // Note: excessive precision ignored because it hides the origin of the numbers used for the
    // ln(1.0->2.0) polynomial
    #[allow(clippy::excessive_precision)]
    pub fn ln(self) -> Self {
        // x may essentially be 1.0 but, as clippy notes, these kinds of
        // floating point comparisons can fail when the bit pattern is not the sames
        if (self - Self::ONE).abs() < f32::EPSILON {
            return Self::ZERO;
        }

        let x_less_than_1 = self < 1.0;

        // Note: we could use the fast inverse approximation here found in super::inv::inv_approx, but
        // the precision of such an approximation is assumed not good enough.
        let x_working = if x_less_than_1 { self.inv() } else { self };

        // according to the SO post ln(x) = ln((2^n)*y)= ln(2^n) + ln(y) = ln(2) * n + ln(y)
        // get exponent value
        let base2_exponent = x_working.extract_exponent_value() as u32;
        let divisor = f32::from_bits(x_working.to_bits() & EXPONENT_MASK);

        // supposedly normalizing between 1.0 and 2.0
        let x_working = x_working / divisor;

        // approximate polynomial generated from maple in the post using Remez Algorithm:
        // https://en.wikipedia.org/wiki/Remez_algorithm
        let ln_1to2_polynomial = -1.741_793_9
            + (2.821_202_6
                + (-1.469_956_8 + (0.447_179_55 - 0.056_570_851 * x_working) * x_working)
                    * x_working)
                * x_working;

        // ln(2) * n + ln(y)
        let result = (base2_exponent as f32) * LN_2 + ln_1to2_polynomial;

        if x_less_than_1 {
            -result
        } else {
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    pub(crate) const MAX_ERROR: f32 = 0.001;

    /// ln(x) test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS: &[(f32, f32)] = &[
        (1e-20, -46.0517),
        (1e-19, -43.749115),
        (1e-18, -41.446533),
        (1e-17, -39.143948),
        (1e-16, -36.841362),
        (1e-15, -34.538776),
        (1e-14, -32.23619),
        (1e-13, -29.933607),
        (1e-12, -27.631021),
        (1e-11, -25.328436),
        (1e-10, -23.02585),
        (1e-09, -20.723267),
        (1e-08, -18.420681),
        (1e-07, -16.118095),
        (1e-06, -13.815511),
        (1e-05, -11.512925),
        (1e-04, -9.2103405),
        (0.001, -6.9077554),
        (0.01, -4.6051702),
        (0.1, -2.3025851),
        (10.0, 2.3025851),
        (100.0, 4.6051702),
        (1000.0, 6.9077554),
        (10000.0, 9.2103405),
        (100000.0, 11.512925),
        (1000000.0, 13.815511),
        (10000000.0, 16.118095),
        (100000000.0, 18.420681),
        (1000000000.0, 20.723267),
        (10000000000.0, 23.02585),
        (100000000000.0, 25.328436),
        (1000000000000.0, 27.631021),
        (10000000000000.0, 29.933607),
        (100000000000000.0, 32.23619),
        (1000000000000000.0, 34.538776),
        (1e+16, 36.841362),
        (1e+17, 39.143948),
        (1e+18, 41.446533),
        (1e+19, 43.749115),
    ];

    #[test]
    fn sanity_check() {
        assert_eq!(F32::ONE.ln(), F32::ZERO);
        for &(x, expected) in TEST_VECTORS {
            let ln_x = F32(x).ln();
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
