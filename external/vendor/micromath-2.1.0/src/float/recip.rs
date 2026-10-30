//! Takes the reciprocal (inverse) of a number, `1/x`.

use super::F32;

impl F32 {
    /// Returns the reciprocal (inverse) of a number, `1/x`.
    pub fn recip(self) -> Self {
        let mut x = self;

        let sx = if x < 0.0 { F32(-1.0) } else { F32(1.0) };
        x *= sx;

        let mut v = F32(f32::from_bits(0x7EF1_27EAu32.wrapping_sub(x.to_bits())));
        let w = x * v;

        // v.0 *= 2.0 - w;
        // v.0 *= 4.0 + w * (-6.0 + w * (4.0 - w));
        v.0 *=
            8.0 + w * (-28.0 + w * (56.0 + w * (-70.0 + w * (56.0 + w * (-28.0 + w * (8.0 - w))))));

        v.0 * sx
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    pub(crate) const MAX_ERROR: f32 = 1e-5;

    pub(crate) const TEST_VECTORS: &[(f32, f32)] = &[
        (0.00001, 100000.0),
        (1.0, 1.0),
        (2.0, 0.5),
        (0.25, 4.0),
        (-0.5, -2.0),
        (core::f32::consts::PI, 1.0 / core::f32::consts::PI),
    ];

    #[test]
    fn sanity_check() {
        assert_eq!(F32(0.0).recip(), F32(core::f32::INFINITY));
        assert_eq!(F32(-0.0).recip(), F32(core::f32::NEG_INFINITY));

        for &(x, expected) in TEST_VECTORS {
            let recip_x = F32(x).recip();
            let relative_error = (recip_x - expected).abs() / expected;

            assert!(
                relative_error <= MAX_ERROR,
                "relative_error {} too large for input {} : {} vs {}",
                relative_error,
                x,
                recip_x,
                expected
            );
        }
    }
}
