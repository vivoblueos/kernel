//! `x^n` with fractional `n` approximation for a single-precision float.

use super::F32;

impl F32 {
    /// Approximates a number raised to a floating point power.
    pub fn powf(self, n: Self) -> Self {
        // using x^n = exp(ln(x^n)) = exp(n*ln(x))
        if self >= Self::ZERO {
            (n * self.ln()).exp()
        } else if !n.is_integer() {
            Self::NAN
        } else if n.is_even() {
            // if n is even, then we know that the result will have no sign, so we can remove it
            (n * self.without_sign().ln()).exp()
        } else {
            // if n isn't even, we need to multiply by -1.0 at the end.
            -(n * self.without_sign().ln()).exp()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    /// error builds up from both exp and ln approximation, so we double the error allowed.
    pub(crate) const MAX_ERROR: f32 = 0.002;

    ///  powf(3,x) test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS_POW3: &[(f32, f32)] = &[
        (-1e-20, 1.0),
        (-1e-19, 1.0),
        (-1e-18, 1.0),
        (-1e-17, 1.0),
        (-1e-16, 0.9999999999999999),
        (-1e-15, 0.9999999999999989),
        (-1e-14, 0.999999999999989),
        (-1e-13, 0.9999999999998901),
        (-1e-12, 0.9999999999989014),
        (-1e-11, 0.9999999999890139),
        (-1e-10, 0.9999999998901388),
        (-1e-09, 0.9999999989013877),
        (-1e-08, 0.9999999890138772),
        (-1e-07, 0.999_999_9),
        (-1e-06, 0.999_998_9),
        (-1e-05, 0.999_989_03),
        (-1e-04, 0.999_890_15),
        (-0.001, 0.998_901_96),
        (-0.01, 0.989_074),
        (-0.1, 0.895_958_5),
        (-1.0, 0.333_333_34),
        (-10.0, 1.693_508_8e-5),
        (-100.0, 0e0),
        (-1000.0, 0.0),
        (1e-20, 1.0),
        (1e-19, 1.0),
        (1e-18, 1.0),
        (1e-17, 1.0),
        (1e-16, 1.0),
        (1e-15, 1.000000000000001),
        (1e-14, 1.0000000000000109),
        (1e-13, 1.00000000000011),
        (1e-12, 1.0000000000010987),
        (1e-11, 1.000000000010986),
        (1e-10, 1.0000000001098612),
        (1e-09, 1.0000000010986123),
        (1e-08, 1.000000010986123),
        (1e-07, 1.000_000_1),
        (1e-06, 1.000_001_1),
        (1e-05, 1.000_011),
        (1e-04, 1.000_109_9),
        (0.001, 1.001_099_2),
        (0.01, 1.011_046_6),
        (0.1, 1.116_123_2),
        (1.0, 3.0),
        (10.0, 59049.0),
    ];

    ///  powf(150,x) test vectors - `(input, output)`
    pub(crate) const TEST_VECTORS_POW150: &[(f32, f32)] = &[
        (-1e-20, 1.0),
        (-1e-19, 1.0),
        (-1e-18, 1.0),
        (-1e-17, 1.0),
        (-1e-16, 0.9999999999999994),
        (-1e-15, 0.999999999999995),
        (-1e-14, 0.9999999999999499),
        (-1e-13, 0.999999999999499),
        (-1e-12, 0.9999999999949893),
        (-1e-11, 0.9999999999498936),
        (-1e-10, 0.9999999994989365),
        (-1e-09, 0.9999999949893649),
        (-1e-08, 0.999_999_94),
        (-1e-07, 0.999_999_5),
        (-1e-06, 0.999_995),
        (-1e-05, 0.999_949_9),
        (-1e-04, 0.999_499_1),
        (-0.001, 0.995_001_9),
        (-0.01, 0.951_128_24),
        (-0.1, 0.605_885_9),
        (-1.0, 0.006_666_667),
        (-10.0, 1.734_153e-22),
        (-100.0, 0e0),
        (-1000.0, 0.0),
        (-10000.0, 0.0),
        (-100000.0, 0.0),
        (-1000000.0, 0.0),
        (-10000000.0, 0.0),
        (-100000000.0, 0.0),
        (-1000000000.0, 0.0),
        (-10000000000.0, 0.0),
        (-100000000000.0, 0.0),
        (-1000000000000.0, 0.0),
        (-10000000000000.0, 0.0),
        (-100000000000000.0, 0.0),
        (-1000000000000000.0, 0.0),
        (-1e+16, 0.0),
        (-1e+17, 0.0),
        (-1e+18, 0.0),
        (-1e+19, 0.0),
        (1e-20, 1.0),
        (1e-19, 1.0),
        (1e-18, 1.0),
        (1e-17, 1.0),
        (1e-16, 1.0000000000000004),
        (1e-15, 1.000000000000005),
        (1e-14, 1.0000000000000502),
        (1e-13, 1.0000000000005012),
        (1e-12, 1.0000000000050107),
        (1e-11, 1.0000000000501064),
        (1e-10, 1.0000000005010636),
        (1e-09, 1.0000000050106352),
        (1e-08, 1.000000050106354),
        (1e-07, 1.000_000_5),
        (1e-06, 1.000_005),
        (1e-05, 1.000_050_1),
        (1e-04, 1.000_501_2),
        (0.001, 1.005_023_2),
        (0.01, 1.051_382_9),
        (0.1, 1.650_475_6),
        (1.0, 150.0),
        (10.0, 5.766_504e21),
    ];

    /// misc powf(x,n) test vectors - `(base_input, power_input, output)`
    pub(crate) const TEST_VECTORS_MISC: &[(f32, f32, f32)] = &[
        (-0.5881598, 2.0, 0.345_931_95),
        (-0.5881598, 3.2, f32::NAN),
        (-0.5881598, 3.0, -0.203_463_27),
        (-1000000.0, 4.0, 1e+24),
    ];

    fn calc_relative_error(experimental: F32, expected: f32) -> F32 {
        if experimental.is_nan() && expected.is_nan() {
            F32::ZERO
        } else if expected != 0.0 {
            (experimental - expected) / expected
        } else {
            (experimental - expected) / (expected + 1.0e-20)
        }
    }

    #[test]
    fn sanity_check() {
        for &(x, expected) in TEST_VECTORS_POW3 {
            let exp_x = F32(3.0).powf(F32(x));
            let relative_error = calc_relative_error(exp_x, expected);

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large for input {} : {} vs {}",
                relative_error,
                x,
                exp_x,
                expected
            );
        }

        for &(x, expected) in TEST_VECTORS_POW150 {
            let exp_x = F32(150.0).powf(F32(x));
            let relative_error = calc_relative_error(exp_x, expected);

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large for input {} : {} vs {}",
                relative_error,
                x,
                exp_x,
                expected
            );
        }

        for &(base_input, power_input, expected) in TEST_VECTORS_MISC {
            let exp_x = F32(base_input).powf(F32(power_input));
            let relative_error = calc_relative_error(exp_x, expected);

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large for input {}.powf({}) : {} vs {}",
                relative_error,
                base_input,
                power_input,
                exp_x,
                expected
            );
        }
    }
}
