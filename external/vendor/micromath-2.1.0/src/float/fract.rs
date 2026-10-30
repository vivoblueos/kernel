//! Floating point fractional number for a single-precision float.

use super::F32;
use super::{EXPONENT_BIAS, MANTISSA_BITS, MANTISSA_MASK};

impl F32 {
    /// Returns the fractional part of a number with sign.
    pub fn fract(self) -> Self {
        let x_bits = self.to_bits();
        let exponent = self.extract_exponent_value();

        // we know it is *only* fraction
        if exponent < 0 {
            return self;
        }

        // find the part of the fraction that would be left over
        let fractional_part = x_bits.overflowing_shl(exponent as u32).0 & MANTISSA_MASK;

        // if there isn't a fraction we can just return 0
        if fractional_part == 0 {
            // TODO: most people don't actually care about -0.0,
            // so would it be better to just not copysign?
            return Self(0.0).copysign(self);
        }

        // Note: alternatively this could use -1.0, but it's assumed subtraction would be more costly
        // example: 'let new_exponent_bits = 127_u32.overflowing_shl(23_u32).0)) - 1.0'
        let exponent_shift: u32 = (fractional_part.leading_zeros() - (32 - MANTISSA_BITS)) + 1;

        let fractional_normalized: u32 =
            fractional_part.overflowing_shl(exponent_shift).0 & MANTISSA_MASK;

        let new_exponent_bits = (EXPONENT_BIAS - (exponent_shift))
            .overflowing_shl(MANTISSA_BITS)
            .0;

        Self::from_bits(fractional_normalized | new_exponent_bits).copysign(self)
    }
}

#[cfg(test)]
mod tests {
    use super::F32;

    #[test]
    fn sanity_check() {
        // fraction check actually won't be the same, though technically exactly accurate
        // so we test by adding back the number removed.
        assert_eq!(F32(2.9).fract().0 + 2.0, 2.9);
        assert_eq!(F32(-1.1).fract().0 - 1.0, -1.1);
        assert_eq!(F32(-0.1).fract().0, -0.1);
        assert_eq!(F32(0.0).fract().0, 0.0);
        assert_eq!(F32(1.0).fract().0 + 1.0, 1.0);
        assert_eq!(F32(1.1).fract().0 + 1.0, 1.1);

        assert_eq!(F32(-100_000_000.13425345345).fract().0, -0.0);
        assert_eq!(F32(100_000_000.13425345345).fract().0, 0.0);
    }
}
