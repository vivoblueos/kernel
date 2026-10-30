//! Exp approximation for a single-precision float.
//!
//! Method described at: <https://stackoverflow.com/a/6985769/2036035>

use super::{EXPONENT_BIAS, F32};
use core::f32::consts;

impl F32 {
    /// Returns `e^(self)`, (the exponential function).
    #[inline]
    pub fn exp(self) -> Self {
        self.exp_ln2_approx(4)
    }

    /// Exp approximation for `f32`.
    pub(crate) fn exp_ln2_approx(self, partial_iter: u32) -> Self {
        if self == Self::ZERO {
            return Self::ONE;
        }

        if (self - Self::ONE).abs() < f32::EPSILON {
            return consts::E.into();
        }

        if (self - (-Self::ONE)).abs() < f32::EPSILON {
            return Self::ONE / consts::E;
        }

        // log base 2(E) == 1/ln(2)
        // x_fract + x_whole = x/ln2_recip
        // ln2*(x_fract + x_whole) = x
        let x_ln2recip = self * consts::LOG2_E;
        let x_fract = x_ln2recip.fract();
        let x_trunc = x_ln2recip.trunc();

        //guaranteed to be 0 < x < 1.0
        let x_fract = x_fract * consts::LN_2;
        let fract_exp = x_fract.exp_smallx(partial_iter);

        //need the 2^n portion, we can just extract that from the whole number exp portion
        let fract_exponent: i32 = fract_exp
            .extract_exponent_value()
            .saturating_add(x_trunc.0 as i32);

        if fract_exponent < -(EXPONENT_BIAS as i32) {
            return Self::ZERO;
        }

        if fract_exponent > ((EXPONENT_BIAS + 1) as i32) {
            return Self::INFINITY;
        }

        fract_exp.set_exponent(fract_exponent)
    }

    /// if x is between 0.0 and 1.0, we can approximate it with the a series
    ///
    /// Series from here:
    /// <https://stackoverflow.com/a/6984495>
    ///
    /// e^x ~= 1 + x(1 + x/2(1 + (x?
    #[inline]
    pub(crate) fn exp_smallx(self, iter: u32) -> Self {
        let mut total = 1.0;

        for i in (1..=iter).rev() {
            total = 1.0 + ((self.0 / (i as f32)) * total);
        }

        Self(total)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    pub(crate) const MAX_ERROR: f32 = 0.001;

    /// exp test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS: &[(f32, f32)] = &[
        (1e-07, 1.0000001),
        (1e-06, 1.000001),
        (1e-05, 1.00001),
        (1e-04, 1.0001),
        (0.001, 1.0010005),
        (0.01, 1.0100502),
        (0.1, 1.105171),
        (1.0, 2.7182817),
        (10.0, 22026.465),
        (-1e-08, 1.0),
        (-1e-07, 0.9999999),
        (-1e-06, 0.999999),
        (-1e-05, 0.99999),
        (-1e-04, 0.9999),
        (-0.001, 0.9990005),
        (-0.01, 0.99004984),
        (-0.1, 0.9048374),
        (-1.0, 0.36787945),
        (-10.0, 4.539_993e-5),
    ];

    #[test]
    fn sanity_check() {
        assert_eq!(F32(-1000000.0).exp(), F32::ZERO);

        for &(x, expected) in TEST_VECTORS {
            let exp_x = F32(x).exp();
            let relative_error = (exp_x - expected).abs() / expected;

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large for input {} : {} vs {}",
                relative_error,
                x,
                exp_x,
                expected
            );
        }
    }
}
